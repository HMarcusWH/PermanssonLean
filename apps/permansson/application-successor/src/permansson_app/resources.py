"""Monotonic shared computation budget with fail-closed work counters.

An operation must explicitly consume work units. This is not OS isolation.
"""
from __future__ import annotations
from dataclasses import dataclass,field
from time import monotonic_ns
from .errors import AppError

@dataclass
class RunBudget:
    max_steps: int
    max_bytes: int
    max_seconds: float
    steps: int=0
    bytes: int=0
    _start: int=field(default_factory=monotonic_ns,repr=False)

    def __post_init__(self):
        if (type(self.max_steps) is not int or type(self.max_bytes) is not int or
            not 1<=self.max_steps<=10_000_000 or not 1<=self.max_bytes<=100_000_000 or
            type(self.max_seconds) not in (int,float) or not 0<self.max_seconds<=3600):
            raise AppError('BUDGET_INPUT','explicit positive bounded run limits required')

    def tick(self,steps:int=1,byte_count:int=0)->None:
        if type(steps) is not int or type(byte_count) is not int or steps<0 or byte_count<0:
            raise AppError('BUDGET_INPUT','usage must be nonnegative integers')
        self.steps+=steps
        self.bytes+=byte_count
        if self.steps>self.max_steps or self.bytes>self.max_bytes:
            raise AppError('BUDGET_EXHAUSTED','shared work or byte limit exceeded')
        self.check_time()

    def check_time(self)->None:
        if (monotonic_ns()-self._start)>self.max_seconds*1_000_000_000:
            raise AppError('BUDGET_TIMEOUT','shared monotonic run deadline exceeded')

    def receipt(self)->dict:
        self.check_time()
        return {'format':'Permansson.App.RunBudget.v1','steps_used':self.steps,
                'bytes_used':self.bytes,'steps_limit':self.max_steps,'bytes_limit':self.max_bytes,
                'deadline_enforced':True,'scientific_claims_verified':False}

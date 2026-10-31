"""Finite residence/first-entry/avoid literal observation automata.

At time t the Markov state Y_t has already been observed. A dwell of m
transitions requires m+1 consecutive target observations. Search and running
are distinct; a first-ever-entry attempt may not be restarted after failure.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from ..errors import AppError
from ..finite_world import FiniteWorld,exact_ratio,parse_finite_world
from ..identity import semantic_identity

FORMAT='Permansson.App.FiniteResidenceRequest.v1'
MODES=('retryable','first_entry','avoid')
SEMANTICS=('entry_by','completion_by')


@dataclass(frozen=True)
class ResidenceProblem:
    model:FiniteWorld
    target:tuple[int,...]
    danger:tuple[int,...]
    mode:str
    deadline:int
    deadline_semantics:str
    dwell_transitions:int
    latest_entry:int
    horizon:int
    initial_law:tuple[Fraction,...]
    semantic_id:dict

    @property
    def monitor_states(self)->tuple[str,...]:
        return ('search',)+tuple(f'run:{k}' for k in range(1,self.dwell_transitions+1))+('failed','success')

    def observe(self,status:str,state:int,time:int)->str:
        if status not in self.monitor_states or type(time) is not int or not 0<=time<=self.horizon:
            raise AppError('RESIDENCE_MONITOR','invalid monitor state or observation time')
        if status in ('success','failed'):return status
        if self.mode=='avoid' and state in self.danger:return 'failed' # danger at success is failure
        if state in self.target:
            if status=='search':
                if time>self.latest_entry:return 'failed'
                return 'success' if self.dwell_transitions==0 else 'run:1'
            seen=int(status.split(':',1)[1])
            return 'success' if seen==self.dwell_transitions else f'run:{seen+1}'
        if status.startswith('run:') and self.mode=='first_entry':return 'failed'
        return 'search' if time<self.latest_entry else 'failed'


def parse_residence(raw:object)->ResidenceProblem:
    keys={'format','model','target','danger','mode','deadline','deadline_semantics',
          'dwell_transitions','initial_law'}
    if type(raw) is not dict or set(raw)!=keys or raw['format']!=FORMAT:
        raise AppError('RESIDENCE_INPUT','finite residence request has wrong schema or version')
    m=parse_finite_world(raw['model'])
    pairs=tuple((s,x) for s in m.strategic for x in m.world)
    if len(pairs)>8 or type(raw['deadline']) is not int or not 0<=raw['deadline']<=8 or type(raw['dwell_transitions']) is not int or not 0<=raw['dwell_transitions']<=4:
        raise AppError('RESIDENCE_SCOPE','bounded <=8 states, deadline <=8 and dwell <=4')
    mode=raw['mode'];semantics=raw['deadline_semantics']
    if mode not in MODES or semantics not in SEMANTICS:
        raise AppError('RESIDENCE_SCOPE','unknown monitor mode or deadline semantics')
    if mode=='avoid' and semantics!='completion_by':
        raise AppError('RESIDENCE_SCOPE','avoid mode requires completion-by deadline')
    deadline=raw['deadline'];dwell=raw['dwell_transitions']
    if semantics=='completion_by' and dwell>deadline:
        raise AppError('RESIDENCE_SCOPE','insufficient observation horizon for dwell')
    latest=deadline if semantics=='entry_by' else deadline-dwell
    horizon=deadline+dwell if semantics=='entry_by' else deadline
    def state_set(key):
        data=raw[key]
        if type(data) is not list or len(data)>len(pairs):raise AppError('RESIDENCE_INPUT',f'{key}: invalid state set')
        out=[]
        for el in data:
            if type(el) is not dict or set(el)!={'strategic','world'} or any(type(el[k]) is not str for k in ('strategic','world')):
                raise AppError('RESIDENCE_INPUT','state reference malformed')
            pair=(el['strategic'],el['world'])
            if pair not in pairs or pairs.index(pair) in out:
                raise AppError('RESIDENCE_INPUT','duplicate/unknown state reference')
            out.append(pairs.index(pair))
        return tuple(sorted(out))
    target,danger=state_set('target'),state_set('danger')
    if not target or (mode!='avoid' and danger) or (mode=='avoid' and not danger):
        raise AppError('RESIDENCE_INPUT','target required; danger only and necessarily in avoid mode')
    initial=raw['initial_law']
    if type(initial) is not list or len(initial)!=len(pairs):
        raise AppError('RESIDENCE_INITIAL','complete initial law required')
    mass=[]
    for row,pair in zip(initial,pairs):
        if type(row) is not dict or set(row)!={'state','mass'} or row['state']!=list(pair):
            raise AppError('RESIDENCE_INITIAL','wrong initial state order or keys')
        mass.append(exact_ratio(row['mass'],probability=True))
    if sum(mass,Fraction(0))!=1:raise AppError('RESIDENCE_INITIAL','initial law must be stochastic')
    semantics_id=semantic_identity('finite-residence-monitor',{
        'model':m.semantic_id(),'target':list(target),'danger':list(danger),
        'mode':mode,'deadline':deadline,'deadline_semantics':semantics,
        'dwell_transitions':dwell,'initial_law':raw['initial_law']})
    return ResidenceProblem(m,target,danger,mode,deadline,semantics,dwell,latest,horizon,tuple(mass),semantics_id)

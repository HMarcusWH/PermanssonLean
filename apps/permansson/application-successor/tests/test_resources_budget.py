"""The whole-run budget itself: limits only shrink, and every limit is enforced.

The mechanism tests run small stand-in child programs under `run_child`, so
each limit is exhausted on purpose and quickly. The CLI-level behaviour of the
26 exact profiles is in test_engine_resource_limits.
"""
from __future__ import annotations
import json
import os
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest import mock

APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app import budget
from permansson_app.errors import AppError

PY=sys.executable
SMALL=budget.Limits(wall_seconds=20,cpu_seconds=2,memory_bytes=200_000_000,output_bytes=50_000,stream_bytes=20_000)
ENV={'PATH':os.environ.get('PATH','/usr/bin')}


class LimitsTests(unittest.TestCase):
    def test_defaults_and_receipt(self):
        self.assertEqual(budget.limits_from_env({}),budget.DEFAULT)
        receipt=budget.DEFAULT.receipt()
        self.assertEqual(receipt['format'],'Permansson.App.WholeRunBudget.v1')
        self.assertEqual(receipt['wall_seconds'],300)
        self.assertEqual(receipt['memory_bytes'],2*1024**3)

    def test_environment_may_only_lower_the_limits(self):
        lowered=budget.limits_from_env({budget.ENV_LIMITS:json.dumps({'cpu_seconds':5,'output_bytes':1000})})
        self.assertEqual((lowered.cpu_seconds,lowered.output_bytes,lowered.wall_seconds),(5,1000,300))
        for raw in ('{"cpu_seconds": 241}','{"memory_bytes": 4294967296}','{"wall_seconds": 0}',
                    '{"wall_seconds": 1.5}','{"wall_seconds": true}','{"unknown": 1}','[1]','not json',
                    '{"output_bytes": "10"}'):
            with self.subTest(raw=raw),self.assertRaises(AppError) as raised:
                budget.limits_from_env({budget.ENV_LIMITS:raw})
            self.assertEqual(raised.exception.code,'BUDGET_INPUT')


@unittest.skipUnless(sys.platform=='linux','the budget is qualified on Linux only')
class EnforcementTests(unittest.TestCase):
    def exhausted(self,program,code,limits=SMALL):
        with self.assertRaises(AppError) as raised:
            budget.run_child([PY,'-c',program],ENV,limits)
        self.assertEqual(raised.exception.code,code,str(raised.exception))

    def test_within_limits_returns_the_streams(self):
        code,out,err=budget.run_child([PY,'-c','import sys;print("ok");print("e",file=sys.stderr)'],ENV,SMALL)
        self.assertEqual((code,out.strip(),err.strip()),(0,b'ok',b'e'))

    def test_cpu_exhaustion(self):
        start=time.monotonic()
        self.exhausted('while True: pass','BUDGET_CPU')
        self.assertLess(time.monotonic()-start,15)

    def test_memory_exhaustion(self):
        self.exhausted('x=bytearray(400_000_000)','BUDGET_MEMORY')

    def test_output_file_exhaustion(self):
        with tempfile.TemporaryDirectory() as td:
            target=Path(td)/'big.bin'
            self.exhausted(f'open({str(target)!r},"wb").write(b"x"*100_000)','BUDGET_OUTPUT')

    def test_stream_exhaustion(self):
        self.exhausted('print("y"*30_000)','BUDGET_STREAM')

    def test_wall_clock_kills_the_whole_process_group(self):
        with tempfile.TemporaryDirectory() as td:
            marker=Path(td)/'child.pid'
            program=('import subprocess,sys,time;'
                     f'p=subprocess.Popen([sys.executable,"-c","import time;time.sleep(60)"]);'
                     f'open({str(marker)!r},"w").write(str(p.pid));time.sleep(60)')
            limits=budget.Limits(wall_seconds=2,cpu_seconds=2,memory_bytes=200_000_000,output_bytes=50_000,
                                 stream_bytes=20_000)
            self.exhausted(program,'BUDGET_TIMEOUT',limits)
            child=int(marker.read_text())
            for _ in range(50):
                if not Path(f'/proc/{child}').exists():
                    break
                time.sleep(0.1)
            self.assertFalse(Path(f'/proc/{child}').exists(),'a grandchild outlived the budget')


class PlatformTests(unittest.TestCase):
    def test_other_platforms_are_refused(self):
        for platform in ('win32','darwin'):
            with self.subTest(platform=platform),mock.patch.object(budget.sys,'platform',platform):
                with self.assertRaises(AppError) as raised:
                    budget.run_child([PY,'-c','pass'],ENV,SMALL)
                self.assertEqual(raised.exception.code,'PLATFORM_UNQUALIFIED')


if __name__=='__main__':
    unittest.main()

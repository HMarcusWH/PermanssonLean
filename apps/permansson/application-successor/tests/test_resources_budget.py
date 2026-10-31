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

    def test_native_allocation_failures_count_as_memory(self):
        # A native crash or abort under the address-space limit is memory exhaustion;
        # any other signal is reported as an aborted run.
        for sig in ('SIGSEGV','SIGBUS','SIGABRT'):
            with self.subTest(signal=sig):
                self.exhausted(f'import os,signal;os.kill(os.getpid(),signal.{sig})','BUDGET_MEMORY')
        self.exhausted('import os,signal;os.kill(os.getpid(),signal.SIGTERM)','BUDGET_ABORTED')

    def test_memory_failures_outside_python_count_as_memory(self):
        # The dynamic loader exits 127 when it cannot map a shared library, and
        # an uncaught ENOMEM ends the interpreter with status 1.
        for program in ('import sys;sys.stderr.write("python: error while loading shared libraries: libm.so.6: '
                        'failed to map segment from shared object\\n");sys.exit(127)',
                        'import errno,os;raise OSError(errno.ENOMEM,os.strerror(errno.ENOMEM))'):
            with self.subTest(program=program):
                self.exhausted(program,'BUDGET_MEMORY')
        # Any other failure is returned to the caller, not relabelled.
        code,_,err=budget.run_child([PY,'-c','raise SystemExit("broken")'],ENV,SMALL)
        self.assertEqual((code,err.strip()),(1,b'broken'))

    def test_startup_ceiling_lies_between_the_limit_and_the_default(self):
        for ceiling in (SMALL.memory_bytes-1,budget.DEFAULT.memory_bytes+1):
            with self.subTest(ceiling=ceiling),self.assertRaises(AppError) as raised:
                budget.run_child([PY,'-c','pass'],ENV,SMALL,startup_address_space=ceiling)
            self.assertEqual(raised.exception.code,'BUDGET_INPUT')
        # A process that lowers its own limit is held to it.
        program=('import resource;resource.setrlimit(resource.RLIMIT_AS,(200_000_000,200_000_000));'
                 'x=bytearray(400_000_000)')
        with self.assertRaises(AppError) as raised:
            budget.run_child([PY,'-c',program],ENV,SMALL,startup_address_space=budget.DEFAULT.memory_bytes)
        self.assertEqual(raised.exception.code,'BUDGET_MEMORY')

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


class MemoryClassificationTests(unittest.TestCase):
    def test_memory_failures_are_recognised_through_the_exception_chain(self):
        import errno
        def chained(outer,inner):
            try:
                try:raise inner
                except BaseException as exc:raise outer from exc
            except BaseException as exc:
                return exc
        for exc in (MemoryError(),OSError(errno.ENOMEM,'Cannot allocate memory'),
                    ImportError('libx.so: failed to map segment from shared object'),
                    chained(ImportError('cannot import name'),MemoryError())):
            with self.subTest(exc=repr(exc)):
                self.assertTrue(budget.is_memory_failure(exc))
        for exc in (ImportError("No module named 'jsonschema'"),OSError(errno.ENOENT,'No such file'),ValueError('x')):
            with self.subTest(exc=repr(exc)):
                self.assertFalse(budget.is_memory_failure(exc))

    def test_a_validator_that_cannot_be_mapped_is_memory_not_a_missing_extra(self):
        import builtins
        from permansson_app import schema_validate
        real=builtins.__import__
        def failing(error):
            def fake(name,*args,**kwargs):
                if name.split('.')[0] in ('jsonschema','referencing'):raise error
                return real(name,*args,**kwargs)
            return fake
        cases=((ImportError('rpds.so: failed to map segment from shared object'),MemoryError,None),
               (ImportError("No module named 'jsonschema'"),AppError,'SCHEMA_DEPENDENCY'))
        for error,expected,code in cases:
            schema_validate._validators.cache_clear()
            with self.subTest(error=str(error)),mock.patch.object(builtins,'__import__',failing(error)):
                with self.assertRaises(expected) as raised:
                    schema_validate._validators()
                if code:self.assertEqual(raised.exception.code,code)
        schema_validate._validators.cache_clear()

    def test_the_child_requires_a_valid_memory_limit(self):
        for raw in (None,'','abc','0',str(budget.DEFAULT.memory_bytes+1)):
            env={} if raw is None else {budget.CHILD_MEMORY_ENV:raw}
            with self.subTest(raw=raw),mock.patch.dict(os.environ,env,clear=False):
                if raw is None:os.environ.pop(budget.CHILD_MEMORY_ENV,None)
                with mock.patch('resource.setrlimit') as setrlimit,self.assertRaises(AppError) as raised:
                    budget.enter_child()
                self.assertEqual(raised.exception.code,'BUDGET_INPUT')
                setrlimit.assert_not_called()


class PlatformTests(unittest.TestCase):
    def test_other_platforms_are_refused(self):
        for platform in ('win32','darwin'):
            with self.subTest(platform=platform),mock.patch.object(budget.sys,'platform',platform):
                with self.assertRaises(AppError) as raised:
                    budget.run_child([PY,'-c','pass'],ENV,SMALL)
                self.assertEqual(raised.exception.code,'PLATFORM_UNQUALIFIED')


if __name__=='__main__':
    unittest.main()

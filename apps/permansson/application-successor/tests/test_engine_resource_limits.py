"""Every exact profile command runs under the whole-run budget (PKG-04).

An exhausted budget leaves no output directory, receipt or staging residue;
an oversized rational input fails closed; a budgeted run publishes exactly the
outputs its child wrote; and the budgeted command set equals the registry.
"""
from __future__ import annotations
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app import budget
from permansson_app.__main__ import BUDGETED_COMMANDS
from permansson_app.capabilities import registry

EX=APP/'src/permansson_app/data/examples'
REQUEST=EX/'private_stage.v1.json'


def run(args,limits=None,tmp=None,extra_env=None,module='permansson_app'):
    env=dict(os.environ,PYTHONPATH=str(APP/'src'),PYTHONDONTWRITEBYTECODE='1')
    env.pop(budget.CHILD_CONFIG_ENV,None)
    env.pop(budget.ENV_LIMITS,None)
    if limits is not None:
        env[budget.ENV_LIMITS]=json.dumps(limits)
    if tmp is not None:
        env['TMPDIR']=str(tmp)
    env.update(extra_env or {})
    return subprocess.run([sys.executable,'-B','-m',module,*map(str,args)],env=env,text=True,
                          capture_output=True,timeout=300)


class CoverageTests(unittest.TestCase):
    def test_every_exact_profile_command_is_budgeted(self):
        self.assertEqual(BUDGETED_COMMANDS,{entry['cli'] for entry in registry()['exact_profiles'].values()})
        self.assertNotIn('run',BUDGETED_COMMANDS)


@unittest.skipUnless(sys.platform=='linux','the budget is qualified on Linux only')
class CommandBudgetTests(unittest.TestCase):
    def setUp(self):
        self.td=Path(tempfile.mkdtemp())
        self.tmp=self.td/'tmp'
        self.tmp.mkdir()
        self.addCleanup(lambda:subprocess.run(['rm','-rf',str(self.td)]))

    def assert_failed_closed(self,proc,out,code):
        self.assertEqual(proc.returncode,2,proc.stdout+proc.stderr)
        self.assertEqual(json.loads(proc.stderr)['error']['code'],code)
        self.assertEqual(proc.stdout,'')
        self.assertFalse(out.exists(),'an exhausted run left an output directory')
        self.assertEqual(list(self.tmp.iterdir()),[],'an exhausted run left staging residue')

    def test_budgeted_run_publishes_exactly_the_child_outputs(self):
        first,second=self.td/'one',self.td/'two'
        for out in (first,second):
            proc=run(['finite-private-stage',REQUEST,'--output',out],tmp=self.tmp)
            self.assertEqual(proc.returncode,0,proc.stderr)
            self.assertEqual(json.loads(proc.stdout)['output'],str(out.absolute()))
        names=sorted(p.name for p in first.iterdir())
        self.assertEqual(names,['independent_check.json','private_stage_receipt.json','scientific_report.json'])
        for name in names:
            self.assertEqual((first/name).read_bytes(),(second/name).read_bytes())
        self.assertEqual(list(self.tmp.iterdir()),[])
        # An existing output is refused before any work, as before.
        proc=run(['finite-private-stage',REQUEST,'--output',first],tmp=self.tmp)
        self.assertEqual(json.loads(proc.stderr)['error']['code'],'OUTPUT_SCOPE')

    def test_output_exhaustion_leaves_nothing(self):
        out=self.td/'out'
        self.assert_failed_closed(run(['finite-private-stage',REQUEST,'--output',out],{'output_bytes':1500},self.tmp),
                                  out,'BUDGET_OUTPUT')

    def test_memory_exhaustion_leaves_nothing(self):
        # Low limits used to fail inside interpreter startup or while mapping a
        # shared library, which surfaced as APP_INTERNAL or SCHEMA_DEPENDENCY.
        # The child now lowers its limit after its code is loaded.
        # These budgets are below the loaded program itself (about 30 MiB), so
        # they are refused deterministically before the request is read.
        for megabytes in (6,12,20):
            out=self.td/f'out{megabytes}'
            with self.subTest(megabytes=megabytes):
                self.assert_failed_closed(run(['finite-private-stage',REQUEST,'--output',out],
                                              {'memory_bytes':megabytes*1_000_000},self.tmp),out,'BUDGET_MEMORY')

    def test_stream_exhaustion_leaves_nothing(self):
        out=self.td/'out'
        self.assert_failed_closed(run(['finite-private-stage',REQUEST,'--output',out],{'stream_bytes':10},self.tmp),
                                  out,'BUDGET_STREAM')

    def test_raising_a_limit_is_refused_before_any_work(self):
        out=self.td/'out'
        self.assert_failed_closed(run(['finite-private-stage',REQUEST,'--output',out],{'cpu_seconds':10_000},self.tmp),
                                  out,'BUDGET_INPUT')

    def forged(self,stage,**limits):
        # What a caller would set to pretend to be the internal child: the
        # current configuration variable and the variables of earlier versions.
        values={'wall_seconds':300,'cpu_seconds':240,'memory_bytes':2*1024**3,'output_bytes':32*1024**2,
                'stream_bytes':1024**2,**limits}
        return {budget.CHILD_CONFIG_ENV:json.dumps({'output':str(stage/'out'),'limits':values}),
                'PERMANSSON_BUDGET_CHILD_OUTPUT':str(stage/'out'),
                'PERMANSSON_BUDGET_CHILD_MEMORY':str(2*1024**3)}

    def private_stage(self):
        stage=self.td/(budget.STAGING_PREFIX+'forged')
        stage.mkdir(mode=0o700)
        return stage

    def test_forged_child_environment_is_ignored(self):
        stage=self.private_stage()
        out=self.td/'out'
        proc=run(['finite-private-stage',REQUEST,'--output',out],tmp=self.tmp,extra_env=self.forged(stage))
        self.assertEqual(proc.returncode,0,proc.stderr)
        self.assertEqual(json.loads(proc.stdout)['output'],str(out.absolute()))
        self.assertEqual(sorted(p.name for p in out.iterdir()),
                         ['independent_check.json','private_stage_receipt.json','scientific_report.json'])
        self.assertEqual(list(stage.iterdir()),[],'the forged staging path was written')
        self.assertEqual(list(self.tmp.iterdir()),[])

    def test_forged_child_environment_cannot_evade_the_limits(self):
        # The public command still runs the parent, which enforces the
        # requested limits: output (child and parent) and the captured streams
        # (parent only).
        for limits,code in (({'output_bytes':1500},'BUDGET_OUTPUT'),({'stream_bytes':10},'BUDGET_STREAM')):
            with self.subTest(code=code):
                stage=self.private_stage() if not (self.td/(budget.STAGING_PREFIX+'forged')).exists() \
                    else self.td/(budget.STAGING_PREFIX+'forged')
                out=self.td/('out-'+code)
                proc=run(['finite-private-stage',REQUEST,'--output',out],limits,self.tmp,
                         extra_env=self.forged(stage))
                self.assert_failed_closed(proc,out,code)
                self.assertEqual(list(stage.iterdir()),[])

    def test_the_internal_entry_point_refuses_an_unissued_staging_path(self):
        cases={'no configuration':{},
               'shared directory':self.forged(self.td),
               'existing output':None}
        taken=self.private_stage();(taken/'out').mkdir();cases['existing output']=self.forged(taken)
        for name,env in cases.items():
            with self.subTest(case=name):
                proc=run(['finite-private-stage',REQUEST,'--output',self.td/'x'],tmp=self.tmp,extra_env=env,
                         module=budget.CHILD_MODULE)
                self.assertEqual(proc.returncode,2,proc.stdout+proc.stderr)
                self.assertEqual(json.loads(proc.stderr)['error']['code'],'BUDGET_CHILD')
                self.assertFalse((self.td/'x').exists())

    def test_the_internal_entry_point_enforces_its_own_limits(self):
        # Even started directly, without the parent, the child stays within the
        # output limit named in its configuration.
        stage=self.private_stage()
        proc=run(['finite-private-stage',REQUEST,'--output',self.td/'x'],tmp=self.tmp,
                 extra_env=self.forged(stage,output_bytes=1500),module=budget.CHILD_MODULE)
        self.assertEqual(proc.returncode,budget.OUTPUT_EXIT,proc.stdout+proc.stderr)
        self.assertEqual(json.loads(proc.stderr)['error']['code'],'BUDGET_OUTPUT')
        self.assertFalse((self.td/'x').exists())

    def test_the_internal_entry_point_runs_only_exact_profiles(self):
        stage=self.private_stage()
        proc=run(['capabilities'],tmp=self.tmp,extra_env=self.forged(stage),module=budget.CHILD_MODULE)
        self.assertEqual(proc.returncode,2,proc.stdout)
        self.assertEqual(json.loads(proc.stderr)['error']['code'],'BUDGET_CHILD')

    def test_oversized_rational_input_fails_closed(self):
        raw=json.loads(REQUEST.read_text())
        huge='1'+'0'*2_000_000
        raw['payoff'][0][0]=huge+'/'+huge[:-1]+'7'
        request=self.td/'huge.json'
        request.write_text(json.dumps(raw))
        out=self.td/'out'
        proc=run(['finite-private-stage',request,'--output',out],tmp=self.tmp)
        self.assertEqual(proc.returncode,2,proc.stdout)
        self.assertNotIn(json.loads(proc.stderr)['error']['code'],{'APP_INTERNAL','BUDGET_ABORTED'})
        self.assertFalse(out.exists())


if __name__=='__main__':
    unittest.main()

"""The documented end-to-end walkthrough keeps working and fails closed.

`scripts/end_to_end.py --lean` additionally compiles every candidate; that
needs the pinned toolchain and is exercised outside the unit suite. These
tests cover the walkthrough's own acceptance logic: a forged independent
check or CLI status must make it fail, the Lean axiom audit must reject
malformed or untrusted records, and a hung compiler process group must be
killed as a whole.
"""
from __future__ import annotations
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import time
import unittest

APP=Path(__file__).resolve().parents[1]
SCRIPT=APP/'scripts/end_to_end.py'
sys.path.insert(0,str(APP/'scripts'))
import end_to_end
sys.path.pop(0)
sys.path.insert(0,str(APP/'src'))
import permansson_app
from permansson_app.capabilities import registry
from permansson_app.proof.lean_candidates import families

REPO=end_to_end.find_repository()
# The installed-distribution test runs this suite in a copy of the application
# whose package code is removed, so `permansson_app` then comes from the wheel.
IMPORTED=Path(permansson_app.__file__).resolve().parent
HAS_SOURCE_PACKAGE=(APP/'src/permansson_app/__init__.py').is_file()
PROFILE='finite-private-stage'

# A stand-in `permansson-app`: runs the real CLI, then forges one output.
WRAPPER='''#!{python}
import json, os, subprocess, sys
from pathlib import Path
env = dict(os.environ, PYTHONPATH={src!r}, PYTHONDONTWRITEBYTECODE='1')
proc = subprocess.run([sys.executable, '-B', '-m', 'permansson_app', *sys.argv[1:]], env=env,
                      text=True, capture_output=True)
mode = os.environ['FORGE_MODE']
if sys.argv[1] == {profile!r} and proc.returncode == 0:
    out = Path(sys.argv[sys.argv.index('--output') + 1])
    check = out / 'independent_check.json'
    data = json.loads(check.read_text())
    reply = json.loads(proc.stdout)
    if mode == 'delete':
        check.unlink()
    elif mode == 'drop-key':
        data.pop('status'); check.write_text(json.dumps(data))
    elif mode.startswith('status='):
        data['status'] = json.loads(mode[len('status='):]); check.write_text(json.dumps(data))
    elif mode.startswith('cli='):
        reply['numeric_status'] = mode[len('cli='):]
    sys.stdout.write(json.dumps(reply))
else:
    sys.stdout.write(proc.stdout)
sys.stderr.write(proc.stderr)
raise SystemExit(proc.returncode)
'''


def _walk(*args,env=None):
    base=os.environ.copy();base['PYTHONDONTWRITEBYTECODE']='1'
    base.update(env or {})
    return subprocess.run([sys.executable,'-B',str(SCRIPT),*args],cwd=APP,env=base,text=True,
                          capture_output=True,timeout=900)


class EndToEndScriptTests(unittest.TestCase):
    def test_walkthrough_covers_every_command_and_family(self):
        commands={entry['cli'] for entry in registry()['exact_profiles'].values()}
        covered={row[0] for row in end_to_end.PROFILES}|{'lp-check'}
        self.assertEqual(commands,covered)
        self.assertEqual({row[3] for row in end_to_end.PROFILES},set(families()))
        for row in end_to_end.PROFILES:
            for name in row[1]:
                self.assertTrue((end_to_end.EXAMPLES/name).is_file(),name)

    def test_walkthrough_passes_from_source(self):
        with tempfile.TemporaryDirectory() as td:
            report=Path(td)/'report.json'
            p=_walk('--report',str(report))
            self.assertEqual(p.returncode,0,p.stdout[-3000:]+p.stderr[-3000:])
            summary=json.loads(report.read_text())
        self.assertEqual((summary['status'],summary['failures']),('PASS',[]))
        rows=[row for row in summary['profiles'] if row['command']!='run']
        self.assertEqual(len(rows),len(end_to_end.PROFILES))
        self.assertGreaterEqual(sum(row.get('lean','').startswith('emitted') for row in rows),20)
        for row in rows:
            self.assertTrue(row['lean'].startswith(('emitted','numeric only: outside the reflection bound')),row)
        native=[row for row in summary['profiles'] if row['command']=='run']
        self.assertEqual(len(native),3)
        # Inside a checkout the native providers run; in a detached copy they are skipped, not failed.
        expected='EXACT_RATIONAL_VERIFIED' if REPO else 'skipped: no repository checkout (pass --source-root)'
        self.assertTrue(all(row['numeric_status']==expected for row in native),native)

    def test_forged_statuses_fail_closed(self):
        """E2E-01: neither a forged checker status nor a forged CLI status is accepted."""
        with tempfile.TemporaryDirectory() as td:
            wrapper=Path(td)/'permansson-app'
            wrapper.write_text(WRAPPER.format(python=sys.executable,src=str(APP/'src'),profile=PROFILE))
            wrapper.chmod(wrapper.stat().st_mode|stat.S_IXUSR)
            # The wrapper is a test double that runs the source tree, so the install check is skipped.
            p=_walk('--app',str(wrapper),'--skip-install-check','--only',PROFILE,env={'FORGE_MODE':'none'})
            self.assertEqual(p.returncode,0,p.stdout[-2000:]+p.stderr[-2000:])
            for mode in ('status="FAIL"','status="SKIPPED"','status="ERROR"','status=null',
                         'status="anything at all"','status=1','drop-key','delete','cli=FAIL'):
                with self.subTest(mode=mode):
                    p=_walk('--app',str(wrapper),'--skip-install-check','--only',PROFILE,env={'FORGE_MODE':mode})
                    self.assertEqual(p.returncode,1,p.stdout[-2000:])
                    self.assertIn('"status": "FAIL"',p.stdout.strip().splitlines()[-1])

    @unittest.skipUnless(HAS_SOURCE_PACKAGE,'no package source to fall back to in this copy')
    def test_source_tree_app_is_not_accepted_as_installed(self):
        """An --app that runs the checkout's source (here by its own sys.path or an inherited
        PYTHONPATH) is refused as an installed-wheel run."""
        with tempfile.TemporaryDirectory() as td:
            app=Path(td)/'permansson-app'
            app.write_text(f'#!{sys.executable}\nimport sys\nsys.path.insert(0, {str(APP/"src")!r})\n'
                           'from permansson_app.__main__ import main\nraise SystemExit(main())\n')
            app.chmod(app.stat().st_mode|stat.S_IXUSR)
            p=_walk('--app',str(app),'--only',PROFILE,env={'PYTHONPATH':str(APP/'src')})
            self.assertEqual(p.returncode,1,p.stdout[-2000:])
            self.assertIn('resolves to the source tree',p.stdout)
        # The installed app never sees an inherited module search path.
        _,env=end_to_end._app_command('/some/installed/permansson-app')
        self.assertNotIn('PYTHONPATH',env)
        self.assertNotIn('PYTHONHOME',env)

    def test_install_check_refuses_reported_source_locations(self):
        """The refusal itself, independent of whether this copy has package source: any `about`
        location in or under src/ is refused, including through a symlink, and a failing
        `about` is an error rather than a pass."""
        with tempfile.TemporaryDirectory() as td:
            app=Path(td)/'permansson-app'
            app.write_text(f'#!{sys.executable}\nimport json, os, sys\n'
                           "if os.environ['ABOUT'] == 'fail':\n    sys.exit(3)\n"
                           "print(json.dumps({'location': os.environ['ABOUT']}))\n")
            app.chmod(app.stat().st_mode|stat.S_IXUSR)
            link=Path(td)/'looks-installed'
            link.symlink_to(APP/'src',target_is_directory=True)
            outside=Path(td)/'site-packages/permansson_app'
            outside.mkdir(parents=True)
            for location in (APP/'src',APP/'src/permansson_app',link/'permansson_app','fail'):
                with self.subTest(location=str(location)):
                    with self.assertRaises(end_to_end.Failure):
                        end_to_end.installed_location(str(app),dict(os.environ,ABOUT=str(location)))
            self.assertEqual(end_to_end.installed_location(str(app),dict(os.environ,ABOUT=str(outside))),
                             outside.resolve())

    def test_about_reports_the_import_location(self):
        env=dict(os.environ,PYTHONPATH=str(APP/'src'),PYTHONDONTWRITEBYTECODE='1')
        p=subprocess.run([sys.executable,'-B','-m','permansson_app','about'],cwd=APP,env=env,text=True,
                         capture_output=True,timeout=60)
        self.assertEqual(p.returncode,0,p.stderr)
        about=json.loads(p.stdout)
        self.assertEqual(Path(about['location']),IMPORTED)
        if HAS_SOURCE_PACKAGE:
            self.assertEqual(IMPORTED,(APP/'src/permansson_app').resolve())
        self.assertEqual(about['lean_status'],'NOT_EXECUTED')

    def test_unknown_only_selection_is_refused(self):
        p=_walk('--only','no-such-profile')
        self.assertEqual(p.returncode,2)

    @unittest.skipUnless(REPO,'needs the repository checkout for the Research replay harness')
    def test_axiom_audit_rejects_untrusted_records(self):
        """E2E-02: the walkthrough uses the harness parser and its whole-log checks."""
        good=("'M.a' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
              "'M.b' does not depend on any axioms\n")
        self.assertEqual(end_to_end.audit_log(REPO,good,['M.a','M.b']),2)
        bad={'duplicate record':good+"'M.a' depends on axioms: [propext]\n",
             'unknown axiom':"'M.a' depends on axioms: [propext, myAxiom]\n'M.b' does not depend on any axioms\n",
             'sorry':"'M.a' depends on axioms: [sorryAx]\n'M.b' does not depend on any axioms\n",
             'missing target':"'M.a' depends on axioms: [propext]\n",
             'extra theorem':good+"'M.c' depends on axioms: [propext]\n",
             'compiler error':"x.lean:3:0: error: unknown identifier\n"+good,
             'malformed list':"'M.a' depends on axioms: [propext Quot.sound]\n'M.b' does not depend on any axioms\n"}
        for label,log in bad.items():
            with self.subTest(label=label),self.assertRaises(end_to_end.Failure):
                end_to_end.audit_log(REPO,log,['M.a','M.b'])

    @unittest.skipUnless(REPO and os.name=='posix','process groups need a POSIX checkout')
    def test_timeout_kills_the_whole_process_group(self):
        """E2E-03: a grandchild that outlives its launcher is killed with it."""
        with tempfile.TemporaryDirectory() as td:
            pidfile=Path(td)/'pid'
            start=time.monotonic()
            with self.assertRaises(end_to_end.Failure):
                end_to_end.run_bounded(REPO,['sh','-c',f'sleep 300 & echo $! > {pidfile}; wait'],Path(td),2)
            self.assertLess(time.monotonic()-start,60)
            pid=int(pidfile.read_text())
            for _ in range(50):
                try:
                    os.kill(pid,0)
                except ProcessLookupError:
                    break
                time.sleep(0.1)
            else:
                self.fail('grandchild survived the timeout')


if __name__=='__main__':
    unittest.main()

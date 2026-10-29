from __future__ import annotations
from copy import deepcopy
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

APP = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(APP / "src"))
from permansson_app.capabilities import registry, selected
from permansson_app.contracts import parse_request
from permansson_app.errors import AppError
from permansson_app.package_data import NAMES, resource_bytes, export_resources
from permansson_app.process import run_bounded
from permansson_app.runner import execute
from permansson_app.source import check_source
from permansson_app.strict_json import strict_loads

ROOT = Path(os.environ.get("PERMANSSON_SOURCE_ROOT", APP.parents[2])).resolve()

class StrictJSONTests(unittest.TestCase):
    def test_empty(self):
        with self.assertRaises(AppError): strict_loads(b"")
    def test_float(self):
        with self.assertRaises(AppError): strict_loads(b'{"a":1.0}')
    def test_nan(self):
        with self.assertRaises(AppError): strict_loads(b'{"a":NaN}')
    def test_duplicate(self):
        with self.assertRaises(AppError): strict_loads(b'{"a":1,"a":2}')
    def test_bad_utf8(self):
        with self.assertRaises(AppError): strict_loads(b'\xff')
    def test_bom(self):
        with self.assertRaises(AppError): strict_loads(b'\xef\xbb\xbf{}')
    def test_surrogate_value(self):
        with self.assertRaises(AppError): strict_loads(b'{"a":"\\ud800"}')
    def test_surrogate_key(self):
        with self.assertRaises(AppError): strict_loads(b'{"\\udfff":0}')
    def test_valid_pair(self):
        self.assertEqual(strict_loads(b'{"a":"\\ud83d\\udc0d"}')["a"], "🐍")
    def test_size(self):
        with self.assertRaises(AppError): strict_loads(b" "*100, max_bytes=10)
    def test_bool_vs_int(self):
        self.assertIs(strict_loads(b'{"n":true}')["n"], True)

class ContractTests(unittest.TestCase):
    def setUp(self):
        self.dir=tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)
        self.p=Path(self.dir.name)
        (self.p/'model.json').write_bytes(resource_bytes('examples/c11.periodic.model.json'))
        self.req=self.p/'request.json'; self.req.write_bytes(b'{}')
    def test_valid(self):
        x={'format':'Permansson.App.NumericRequest.v1','capability':'c11.stationary_1_to_6.numeric.v1','input_file':'model.json'}
        self.assertEqual(parse_request(x,request_file=self.req).model_path,self.p/'model.json')
    def test_missing_key(self):
        with self.assertRaises(AppError): parse_request({'format':'Permansson.App.NumericRequest.v1'},request_file=self.req)
    def test_escape(self):
        v={'format':'Permansson.App.NumericRequest.v1','capability':'abc','input_file':'../abc'}
        with self.assertRaises(AppError): parse_request(v,request_file=self.req)
    def test_absolute(self):
        v={'format':'Permansson.App.NumericRequest.v1','capability':'abc','input_file':'/etc/passwd'}
        with self.assertRaises(AppError): parse_request(v,request_file=self.req)
    def test_symlink(self):
        (self.p/'symlink.json').symlink_to(self.p/'model.json')
        v={'format':'Permansson.App.NumericRequest.v1','capability':'abc','input_file':'symlink.json'}
        with self.assertRaises(AppError): parse_request(v,request_file=self.req)
    def test_unknown_capability(self):
        with self.assertRaises(AppError): selected('fake')

class ResourcesTests(unittest.TestCase):
    def test_all_resource_names(self):
        self.assertEqual(len(NAMES),10)
        for name in NAMES: self.assertGreater(len(resource_bytes(name)),0)
    def test_export_is_identical(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'resources'
            hashes=export_resources(p)
            for name,expect in hashes.items():
                self.assertEqual(hashlib.sha256((p/name).read_bytes()).hexdigest(),expect)
    def test_export_refuses_existing(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(AppError): export_resources(Path(d))
    def test_pins(self):
        if not (ROOT/'verification/research').is_dir(): self.skipTest('no source checkout provided')
        for cap in registry()['capabilities'].values():
            self.assertEqual(check_source(ROOT,cap['sha256_pins']),cap['sha256_pins'])
    def test_missing_pins_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(AppError):
                check_source(Path(d),{'verification/research/expected.py':'0'*64})

class ProcessTests(unittest.TestCase):
    def test_short(self):
        with tempfile.TemporaryDirectory() as d:
            log=Path(d)/'log.txt'
            run_bounded([sys.executable,'-c',"print('hello')"],Path(d),log,timeout=5)
            self.assertEqual(log.read_text().strip(),'hello')
    def test_nonzero(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(AppError) as cm:
                run_bounded([sys.executable,'-c','exit(3)'],Path(d),Path(d)/'log.txt',timeout=5)
            self.assertEqual(cm.exception.code,'PROCESS_FAILED')
    def test_output_cap(self):
        with tempfile.TemporaryDirectory() as d:
            script="import os,time;os.write(1,b'abcdefghi');time.sleep(.5)"
            with self.assertRaises(AppError) as cm:
                run_bounded([sys.executable,'-c',script],Path(d),Path(d)/'log.txt',timeout=3,max_output=8)
            self.assertEqual(cm.exception.code,'PROCESS_OUTPUT')
    def test_timeout(self):
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(AppError) as cm:
                run_bounded([sys.executable,'-c','import time;time.sleep(2)'],Path(d),Path(d)/'log.txt',timeout=.08)
            self.assertEqual(cm.exception.code,'PROCESS_TIMEOUT')

class NativeNumericTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not (ROOT/'verification/research/c10_exact_execution.py').is_file():
            raise unittest.SkipTest('Set PERMANSSON_SOURCE_ROOT to audited extracted repository')
    def case(self,name):
        d=tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        base=Path(d.name)
        for suffix in ('model','request'):
            (base/f'{name}.{suffix}.json').write_bytes(resource_bytes(f'examples/{name}.{suffix}.json'))
        return base, base/f'{name}.request.json'
    def test_c10(self):
        d,req=self.case('c10');v=execute(req,ROOT,d/'run')
        self.assertEqual(v['capability'],'c10.fixed_six_state.numeric.v1')
        self.assertEqual(v['native_summary']['numeric_selected'],'full')
        self.assertEqual(v['native_summary']['numeric_optimum'],'1')
        self.assertEqual(v['lean_status'],'NOT_EXECUTED')
        self.assertFalse(v['scientific_claims_verified'])
    def test_c11_multiclass(self):
        d,req=self.case('c11.multiclass');v=execute(req,ROOT,d/'run')
        self.assertEqual(v['native_summary']['bottom_classes'],2)
        self.assertEqual(v['numeric_status'],'EXACT_RATIONAL_VERIFIED')
    def test_c11_periodic(self):
        d,req=self.case('c11.periodic');v=execute(req,ROOT,d/'run')
        self.assertEqual(v['native_summary']['bottom_classes'],1)
    def test_reuse_output(self):
        d,req=self.case('c11.periodic'); out=d/'run';execute(req,ROOT,out)
        with self.assertRaises(AppError) as cm: execute(req,ROOT,out)
        self.assertEqual(cm.exception.code,'OUTPUT_SCOPE')
    def test_inside_repo_blocked(self):
        d,req=self.case('c10');
        with self.assertRaises(AppError) as cm: execute(req,ROOT,ROOT/'tmp_bad_out')
        self.assertEqual(cm.exception.code,'OUTPUT_SCOPE')
    def test_changed_c10_input(self):
        d,req=self.case('c10'); p=d/'c10.model.json'
        text=p.read_text(); p.write_text(text.replace('"1/2"','"1/3"',1))
        with self.assertRaises(AppError) as cm: execute(req,ROOT,d/'run')
        self.assertEqual(cm.exception.code,'PROCESS_FAILED')
    def test_seven_state_rejected(self):
        d,req=self.case('c11.periodic'); p=d/'c11.periodic.model.json'
        data={'n':7,'matrix':[['1' if i==j else '0' for j in range(7)] for i in range(7)],'descriptor':[True]*7}
        p.write_text(json.dumps(data));
        with self.assertRaises(AppError): execute(req,ROOT,d/'run')
    def test_source_pin_failure(self):
        d,req=self.case('c10');
        fake=d/"empty";fake.mkdir()
        with self.assertRaises(AppError) as cm: execute(req,fake,d/'run')
        self.assertEqual(cm.exception.code,'SOURCE_UNVERIFIED')
    def test_native_saved_receipt_was_checked(self):
        d,req=self.case('c11.multiclass');v=execute(req,ROOT,d/'run')
        self.assertIn(b'PASS',(d/'run/checker.log').read_bytes())
        self.assertEqual(v['artifacts']['native_receipt']['sha256'],hashlib.sha256((d/'run/native/numeric_receipt.json').read_bytes()).hexdigest())

if __name__=='__main__': unittest.main()

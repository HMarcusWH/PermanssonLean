"""Mock-only candidate preparation regressions; never approves 45/11."""
import json
from unittest import TestCase, mock

import final_closure_assemble_v3 as mod

H = "a"*40
SHA = mod.digest

class AssemblyV3Tests(TestCase):
    def test_valid_compiler_member_is_bound_to_actual_shard(self):
        compiler_log = b"kernel elaborated type and axioms"
        source = b"theorem genuine : True := by trivial\n"
        record = {
            "inventory_index": 1, "id":"all:0001",
            "head_sha":H, "path":"Proof.lean",
            "declaration":"Test.genuine", "source_sha256":SHA(source),
            "case_ids":["C-01"], "claim_ids":[],
            "compiler_result":"PASS", "compiler_check":"research",
            "check_run_id":None,"axiom_log_member":"axiom_logs/all_0001.log",
            "axiom_log_sha256":SHA(compiler_log),
            "elaborated_type_sha256":"b"*64,"declaration_kind":"theorem",
            "universe_params_repr":"[]","transitive_axioms":[],
        }
        producer = {"actual_check_run_id":83,"artifact_id":99}
        compiled = {"declaration_kind":"theorem","universe_params_repr":"[]"}
        with mock.patch.object(mod, "exact_source_bytes", return_value=source), \
             mock.patch.object(mod, "compiled_type_record",return_value=compiled), \
             mock.patch.object(mod, "elaborated_type_sha256",return_value="b"*64), \
             mock.patch.object(mod, "parse_target_axioms",return_value=[]):
            observed=mod.proof_row(
                H, record, producer, compiler_log,
                "compiler/axiom_logs/all_0001.log")
            self.assertEqual(observed["check_run_id"],83)
            self.assertEqual(observed["producer_artifact_id"],99)
            self.assertEqual(observed["statement_sha256"],"b"*64)
            self.assertEqual(observed["compiler_check"],"pr113-compiler-shard")
            self.assertEqual(observed["producer_member_bindings"],[
                {"outer_member":"compiler/axiom_logs/all_0001.log",
                 "source_member":"axiom_logs/all_0001.log"}])
            corrupted=dict(record, elaborated_type_sha256="c"*64)
            with self.assertRaises(mod.AssemblyError):
                mod.proof_row(H, corrupted, producer, compiler_log,
                              "compiler/axiom_logs/all_0001.log")

    def test_exact_append_case_preserves_positive_and_negative_source_bytes(self):
        original=b"theorem actual : True := by trivial\n"
        mutant=original+b"\nexample : False := by exact actual\n"
        positive_log=b"positive compiled\n"
        negative_log=b"error: unsolved goals\n"
        test_bytes=b"def test_original():\n    pass\n"
        record={
            "case_id":"C-01","source_head":H,
            "independent_review":False,
            "mutation_record":{
                "id":"C-01_test_original","head_sha":H,
                "test_path":"verification/research/test_original.py",
                "test_name":"test_original","source_sha256":SHA(test_bytes),
                "case_ids":["C-01"],"claim_ids":[],
                "original_lean_source_path":"Proof.lean",
                "original_lean_source_member":"orig.lean",
                "original_lean_source_sha256":SHA(original),
                "mutant_source_member":"mut.lean",
                "mutant_source_sha256":SHA(mutant),
                "positive_control":{"compiled":True,"exit_code":0,
                    "lean_toolchain":"4.34.0",
                    "log_member":"pos.log","log_sha256":SHA(positive_log)},
                "outcome":"REJECTED_SEMANTIC","compiler_exit_code":1,
                "log_member":"neg.log","log_sha256":SHA(negative_log),
                "check_run_id":None,
            }
        }
        content={
            "C-01/unreviewed_candidate.json":json.dumps(record).encode(),
            "C-01/source_logs/orig.lean":original,
            "C-01/source_logs/mut.lean":mutant,
            "C-01/source_logs/pos.log":positive_log,
            "C-01/source_logs/neg.log":negative_log,
        }
        def frozen(_head,path):
            return test_bytes if path.endswith(".py") else original
        sealed={}
        with mock.patch.object(mod, "exact_source_bytes",side_effect=frozen):
            p,n=mod.append_case_rows(
                H,"C-01",{"actual_check_run_id":88,"artifact_id":177},
                content,sealed)
        self.assertEqual(len(sealed),4)
        self.assertEqual(p["check_run_id"],88)
        self.assertEqual(n["producer_artifact_id"],177)
        self.assertEqual(p["positive_control"]["log_member"],p["log_member"])
        self.assertEqual(n["positive_control"]["log_member"],p["log_member"])
        self.assertEqual(len(n["producer_member_bindings"]),4)
        self.assertEqual(n["case_ids"],["C-01"])
        content["C-01/source_logs/mut.lean"]=b"altered"
        with mock.patch.object(mod, "exact_source_bytes",side_effect=frozen):
            with self.assertRaises(mod.AssemblyError):
                mod.append_case_rows(
                    H,"C-01",{"actual_check_run_id":88,"artifact_id":177},
                    content,{})

    def test_rejects_unsafe_members_and_duplicate_evidence(self):
        items={}
        mod.pack_member(items,"proof/proof.log",b"genuine")
        for path in ("proof/proof.log","../escape","/absolute",
                     "a\\b"):
            with self.subTest(path=path),self.assertRaises(mod.AssemblyError):
                mod.pack_member(items,path,b"danger")

    def test_gap_report_never_claims_mathematical_acceptance(self):
        self.assertEqual(mod.FORMAT_V3,
                         "Permansson.FinalClosureDetachedReceipts.v3")

"""25+5 workflow profile mutation gates. No security approval is fabricated."""
import ast
import copy
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
import types
from unittest import mock

import pr113_successor_workflow_profile as p

H="a"*40


def fixture():
    approved={f"original-{i:02}.yml":p.digest(
        f"name: original {i}\n".encode()) for i in range(25)}
    contents={".github/workflows/"+n:
              f"name: original {i}\n".encode()
              for i,n in enumerate(approved)}
    rows=[]
    proposed=sorted(p.PROPOSED)
    for name in proposed:
        staged=p.STAGED_PREFIX+name
        data=(
            "# REVIEW PENDING\n"
            f"name: PR113 {name}\n"
            "on:\n  push:\n    branches: [research/final-mathematical-closure]\n"
            "permissions:\n  contents: read\n"
            "jobs:\n"
            "  fixture:\n"
            "    steps:\n"
            "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262\n"
        )
        if name=="pr113-source-controls-v3_1.yml":
            data+=(
                "  original-legacy20:\n"
                "    name: legacy\n"
                "  original-legacy20-replay:\n"
                "    if: github.event_name == 'workflow_dispatch'\n"
                "    run: pr113_legacy20_choice_delivery.py\n"
                "    review_comment_id:\n"
            )
        raw=data.encode()
        contents[staged]=raw
        rows.append({
            "workflow_path":".github/workflows/"+name,
            "staged_source_path":staged,
            "git_blob_oid":p.git_blob_oid(raw),
            "source_unchanged":False,"approved":False,"installed":False,
        })
    manifest={
        "format":"Permansson.PR113.UnreviewedWorkflowProposals.v1",
        "status":"SOURCE_STAGED_NONEXECUTABLE_PENDING_INDEPENDENT_SECURITY_REVIEW",
        "original_approved_workflow_count":25,
        "historic_T":p.T,"base_B":p.B113,
        "independent_security_review":False,
        "owner_authorized_activation":False,
        "mathematical_acceptance":False,
        "release_authorized":False,
        "proposals":rows,
    }
    contents[p.MANIFEST]=json.dumps(manifest).encode()
    listing=("\n".join(sorted(".github/workflows/"+n
                              for n in approved))+"\n").encode()
    return approved,contents,listing


class WorkflowProfileTests(unittest.TestCase):
    def test_explicit_25_plus_5_not_activation(self):
        approved,files,tree=fixture()
        report=p.audit(H,read=files.__getitem__,
                       tree=lambda:tree,approved=approved)
        self.assertEqual(report["original_workflow_count"],25)
        self.assertEqual(report["proposed_future_workflow_count"],30)
        self.assertFalse(report["independent_security_review"])
        self.assertFalse(report["owner_activation_authorized"])
        self.assertFalse(report["publication_authorized"])

    def test_new_active_file_not_granted_historical_status(self):
        approved,files,tree=fixture()
        tree+=b".github/workflows/unreviewed.yml\n"
        with self.assertRaises(p.ProfileError):
            p.audit(H,read=files.__getitem__,tree=lambda:tree,approved=approved)

    def test_original_workflow_bytes_remain_immutable(self):
        approved,files,tree=fixture()
        files[".github/workflows/original-00.yml"]=b"permissions: write\n"
        with self.assertRaises(p.ProfileError):
            p.audit(H,read=files.__getitem__,tree=lambda:tree,approved=approved)

    def test_modified_staged_bytes_and_unpinned_action_rejected(self):
        approved,files,tree=fixture()
        target=p.STAGED_PREFIX+"pr113-preseal-fullscope.yml"
        files[target]+=b"  checks: write\n"
        with self.assertRaises(p.ProfileError):
            p.audit(H,read=files.__getitem__,tree=lambda:tree,approved=approved)
        approved,files,tree=fixture()
        row=json.loads(files[p.MANIFEST])
        files[target]+=b"  checks: write\n"
        rec=next(x for x in row["proposals"] if
                 x["staged_source_path"]==target)
        rec["git_blob_oid"]=p.git_blob_oid(files[target])
        files[p.MANIFEST]=json.dumps(row).encode()
        with self.assertRaises(p.ProfileError):
            p.audit(H,read=files.__getitem__,tree=lambda:tree,approved=approved)

    def test_direct_cli_imports_workflow_contract_without_pythonpath(self):
        script=Path(p.__file__).resolve()
        env=os.environ.copy()
        env.pop("PYTHONPATH",None)
        done=subprocess.run(
            [sys.executable,"-B",str(script),"--head","invalid-head",
             "--out",str(script.parent/"NEVER_WRITTEN.json")],
            cwd=p.ROOT,env=env,capture_output=True,text=True,timeout=20)
        self.assertEqual(done.returncode,2,done.stderr)
        self.assertIn("WORKFLOW PROFILE NOT ACCEPTED",done.stderr)
        self.assertNotIn("ModuleNotFoundError",done.stderr)


    def test_real_immutable_historical_25_git_allowlist(self):
        head=p.git_bytes("HEAD",op=("rev-parse","HEAD")).decode().strip()
        historical=p.authenticated_historical_25(head)
        self.assertEqual(len(historical),25)
        self.assertTrue(all(len(v)==64 for v in historical.values()))
        self.assertEqual(p.HISTORICAL_25_HEAD,
                         "5189f0c4a0db7535d57a9ff2a7aef6a3e76191b6")
        self.assertEqual(p.HISTORICAL_CONTRACT_BLOB,
                         "f8fa8196a7a0e33d2f218faa0ba570c09aac9a3a")
        self.assertNotIn("pr113-historical-migration-candidates.yml",historical)
        self.assertNotEqual(next(iter(historical.values())),
                            "02e97e27e85b9d3353edf495eab1ee8cb8b9e642")
        original=p.git_bytes(p.HISTORICAL_25_HEAD,p.HISTORICAL_CONTRACT)
        self.assertEqual(p.parse_historical_25_contract(original),historical)

    def test_historical_contract_parser_rejects_24_26_duplicate_dynamic_and_oid(self):
        original=p.git_bytes(p.HISTORICAL_25_HEAD,p.HISTORICAL_CONTRACT)
        syntax=ast.parse(original)
        table=next(item.value for item in syntax.body
                   if isinstance(item,ast.Assign)
                   and any(isinstance(t,ast.Name) and
                           t.id=="APPROVED_WORKFLOWS" for t in item.targets))
        constant=next(item.value for item in syntax.body
                      if isinstance(item,ast.Assign)
                      and any(isinstance(t,ast.Name) and
                              t.id=="APPROVED_WORKFLOW_SHA256"
                              for t in item.targets))
        self.assertIsInstance(table,ast.Dict)
        self.assertEqual(len(table.keys),25)
        for variant in ("24","26","duplicate","dynamic","git_oid","wrong_constant"):
            altered=copy.deepcopy(syntax)
            mapped=next(item.value for item in altered.body
                        if isinstance(item,ast.Assign)
                        and any(isinstance(t,ast.Name) and
                                t.id=="APPROVED_WORKFLOWS" for t in item.targets))
            literal=next(item.value for item in altered.body
                         if isinstance(item,ast.Assign)
                         and any(isinstance(t,ast.Name) and
                                 t.id=="APPROVED_WORKFLOW_SHA256"
                                 for t in item.targets))
            if variant=="24":
                mapped.keys.pop()
                mapped.values.pop()
            elif variant=="26":
                mapped.keys.append(copy.deepcopy(mapped.keys[0]))
                mapped.values.append(copy.deepcopy(mapped.values[0]))
            elif variant=="duplicate":
                mapped.keys[-1]=copy.deepcopy(mapped.keys[0])
            elif variant=="dynamic":
                mapped.values[0]=ast.Call(
                    func=ast.Name(id="eval",ctx=ast.Load()),
                    args=[ast.Constant(value="'untrusted'")],keywords=[])
            elif variant=="git_oid":
                mapped.values[0]=ast.Constant(value="a"*40)
            else:
                literal.value="b"*40
            with self.subTest(variant=variant),self.assertRaises(p.ProfileError):
                p.parse_historical_25_contract(
                    ast.unparse(ast.fix_missing_locations(altered)).encode())

    def test_frozen_git_contract_rejects_spoofed_bytes_and_wrong_tree(self):
        real=p.git_bytes
        anchor=p.HISTORICAL_25_HEAD
        def tamper(head,path=None,*,op=None):
            if head==anchor and path==p.HISTORICAL_CONTRACT and op is None:
                return real(head,path)+b"\n# unapproved historical change\n"
            return real(head,path,op=op)
        with mock.patch.object(p,"git_bytes",side_effect=tamper):
            with self.assertRaisesRegex(p.ProfileError,
                                        "Git blob byte identity changed"):
                p.authenticated_historical_25()
        def wrong_tree(head,path=None,*,op=None):
            if op==("ls-tree","-r","-z",anchor,"--",".github/workflows"):
                data=real(head,path,op=op)
                self.assertIn(b"100644 blob ",data)
                return data.replace(b"100644 blob ",b"100755 blob ",1)
            return real(head,path,op=op)
        with mock.patch.object(p,"git_bytes",side_effect=wrong_tree):
            with self.assertRaisesRegex(p.ProfileError,
                                        "Git mode unexpected"):
                p.authenticated_historical_25()

    def test_legacy_modules_import_with_current_v2_only_namespace(self):
        """An installed 30 Git-OID contract may not masquerade as 25 SHA256s."""
        fake=types.ModuleType("verification.integrity.workflow_contract")
        fake.APPROVED_WORKFLOW_BLOBS={"research-lean.yml":"a"*40}
        real_path=Path(p.__file__).resolve()
        atomic_path=real_path.with_name("pr113_atomic_migration_preview.py")
        with mock.patch.dict(sys.modules,{
                "verification.integrity.workflow_contract":fake}):
            for label,path in (("legacy_25",real_path),
                               ("atomic_preview",atomic_path)):
                spec=importlib.util.spec_from_file_location(
                    "pr113_v2_import_canary_"+label,path)
                self.assertIsNotNone(spec)
                candidate=importlib.util.module_from_spec(spec)
                spec.loader.exec_module(candidate)
                self.assertTrue(callable(candidate.preview if
                        label=="atomic_preview" else candidate.audit))
                if label=="atomic_preview":
                    self.assertEqual(
                        candidate.preview.__kwdefaults__["old_audit"],None)
        self.assertFalse(hasattr(fake,"APPROVED_WORKFLOWS"))

    def test_fake_owner_authorization_in_staged_manifest_rejected(self):
        approved,files,tree=fixture()
        record=json.loads(files[p.MANIFEST])
        record["owner_authorized_activation"]=True
        files[p.MANIFEST]=json.dumps(record).encode()
        with self.assertRaises(p.ProfileError):
            p.audit(H,read=files.__getitem__,tree=lambda:tree,approved=approved)


if __name__=="__main__":
    unittest.main()

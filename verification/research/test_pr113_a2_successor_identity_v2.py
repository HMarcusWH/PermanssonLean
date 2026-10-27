"""Versioned A2 current-30 source invariants; historical verifiers are untouched."""
import unittest
import hashlib
import json
import subprocess
import copy
import pr113_workflow_profile_v2 as workflow_profile
from unittest import mock
from pathlib import Path
import localized_prefix_support as frozen
import pr113_a2_successor_identity as legacy
import pr113_a2_successor_identity_v2 as successor


def fixture():
    old={path:("100644","a"*40)
         for path in successor.PINNED_MODIFIED_PROVIDERS}
    old.update({
        "PermanssonResearch.lean":("100644",frozen.ROOT_BLOB),
        "lean-toolchain":("100644","b"*40),
        "lake-manifest.json":("100644","c"*40),
        "README.md":("100644","d"*40),
    })
    newer=dict(old)
    # This test did not exist at original PR79 BASE.
    assert successor.LATE_A2_TEST not in old
    newer[successor.LATE_A2_TEST]=(
        "100644",successor.LATE_A2_TEST_PROPOSED_BLOB)
    for path,oid in successor.PINNED_MODIFIED_PROVIDERS.items():
        newer[path]=("100644",oid)
    newer["PermanssonResearch.lean"]=("100644","e"*40)
    newer["README.md"]=("100644","f"*40)
    for path,oid in frozen.ACCEPTED_A2_PROOF_BLOBS.items():
        newer[path]=("100644",oid)
    for path,oid in successor.INHERITED_A2_VERIFIERS.items():
        newer[path]=("100644",oid)
    return old,newer


class SuccessorA2Active30Tests(unittest.TestCase):
    def test_exact_twelve_original_modified_and_one_historically_late_test(self):
        old,current=fixture()
        report=successor.reconcile(old,current)
        self.assertEqual(len(report["pinned_successor_provider_paths"]),12)
        self.assertNotIn(successor.LATE_A2_TEST,old)
        self.assertEqual(report["late_introduced_A2_test"],successor.LATE_A2_TEST)
        self.assertEqual(report["late_A2_original_introducer"],
                         successor.HISTORICAL_A2_INTRODUCER)
        self.assertEqual(report["late_A2_original_blob"],
                         successor.LATE_A2_TEST_ORIGINAL_BLOB)
        self.assertEqual(len(successor.INHERITED_A2_VERIFIERS),2)
        self.assertEqual(len(legacy.INHERITED_A2_VERIFIERS),3)
        self.assertEqual(len(frozen.ACCEPTED_A2_PROOF_BLOBS),4)
        # Three independent source identities replace the obsolete frozen
        # *successor* literal. The historical original stays immutable.
        root = Path(__file__).resolve().parents[2]
        staged = ("docs/operations/pr113_required_gate_replacement_unapproved/"
                  "test_localized_prefix_compiler.py")
        manifest_path = ("docs/operations/pr113_required_gate_replacement_unapproved/"
                         "manifest.json")
        manifest = json.loads((root / manifest_path).read_bytes())
        self.assertEqual(manifest["format"],
                         "Permansson.PR113.UnapprovedRequiredGateTransition.v1")
        matching = [record for record in manifest["staged_replacements"]
                    if record.get("target") == successor.LATE_A2_TEST]
        self.assertEqual(len(matching), 1)
        record = matching[0]
        self.assertEqual(record["source"], staged)
        self.assertIs(record["installed"], False)
        self.assertIs(record["independent_reviewed"], False)
        payload = (root / staged).read_bytes()
        computed = hashlib.sha1(
            b"blob " + str(len(payload)).encode("ascii") + b"\0" + payload
        ).hexdigest()
        committed = subprocess.check_output(
            ["git", "rev-parse", "HEAD:" + staged], cwd=root,
            text=True, stderr=subprocess.DEVNULL, timeout=20,
        ).strip()
        self.assertEqual(computed, committed)
        self.assertEqual(record["git_blob_oid"], committed)
        self.assertEqual(successor.LATE_A2_TEST_PROPOSED_BLOB, committed)
        self.assertEqual(report["late_A2_proposed_blob"], committed)
        self.assertNotEqual(committed, successor.LATE_A2_TEST_ORIGINAL_BLOB)
        self.assertNotEqual(
            successor.PINNED_MODIFIED_PROVIDERS[
                "verification/integrity/workflow_contract.py"],
            legacy.PINNED_MODIFIED_PROVIDERS[
                "verification/integrity/workflow_contract.py"])

    def test_a2_source_pin_delta_is_exact_and_no_wildcard(self):
        old,current=fixture()
        for changed in successor.PINNED_MODIFIED_PROVIDERS:
            altered=dict(current)
            altered[changed]=("100644","0"*40)
            with self.subTest(changed=changed),self.assertRaises(frozen.GuardError):
                successor.reconcile(old,altered)
        for candidate in ("0000000000000000000000000000000000000000",
                          successor.LATE_A2_TEST_ORIGINAL_BLOB):
            changed=dict(current)
            changed[successor.LATE_A2_TEST]=("100644",candidate)
            with self.assertRaises(frozen.GuardError):
                successor.reconcile(old,changed)
        absent=dict(current)
        absent.pop(successor.LATE_A2_TEST)
        with self.assertRaises(frozen.GuardError):
            successor.reconcile(old,absent)
        spoofed=dict(old)
        spoofed[successor.LATE_A2_TEST]=(
            "100644",successor.LATE_A2_TEST_ORIGINAL_BLOB)
        with self.assertRaises(frozen.GuardError):
            successor.reconcile(spoofed,current)
        for protected in successor.INHERITED_A2_VERIFIERS:
            altered=dict(current)
            altered[protected]=("100644","1"*40)
            with self.subTest(protected=protected),self.assertRaises(frozen.GuardError):
                successor.reconcile(old,altered)

    def test_v1_preactivation_receipt_cannot_satisfy_v2(self):
        old,current=fixture()
        previous=dict(current)
        old_pin=legacy.PINNED_MODIFIED_PROVIDERS[
            "verification/integrity/workflow_contract.py"]
        previous["verification/integrity/workflow_contract.py"]=("100644",old_pin)
        with self.assertRaises(frozen.GuardError):
            successor.reconcile(old,previous)
        self.assertNotEqual(successor.FORMAT,legacy.FORMAT)

    def test_new_unapproved_mathematical_provider_not_allowed(self):
        old,current=fixture()
        old["PermanssonResearch/InjectedTheorem.lean"]=("100644","1"*40)
        current["PermanssonResearch/InjectedTheorem.lean"]=("100644","2"*40)
        with self.assertRaises(frozen.GuardError):
            successor.reconcile(old,current)

    def test_ordered_direct_H_and_synthetic_S_identity(self):
        B=successor.PR113_BASE
        H="a"*40
        S="b"*40
        TREE="c"*40
        def authenticated(root,*args):
            mapping={
                ("rev-parse","HEAD"):S,
                ("rev-parse",H+"^{tree}"):TREE,
                ("rev-parse","HEAD^{tree}"):TREE,
                ("show","-s","--format=%P",S):B+" "+H,
            }
            return mapping[args]
        with mock.patch.object(frozen,"git_text",side_effect=authenticated):
            self.assertEqual(
                successor.check_checkout_identity(Path("."),H),(S,TREE))
        def direct(root,*args):
            if args==("rev-parse","HEAD"):
                return H
            return authenticated(root,*args)
        with mock.patch.object(frozen,"git_text",side_effect=direct):
            self.assertEqual(
                successor.check_checkout_identity(Path("."),H),(H,TREE))
        for parents in (H+" "+B,B+" "+"d"*40,B+" "+H+" "+"e"*40):
            def fake(root,*args):
                if args==("show","-s","--format=%P",S):
                    return parents
                return authenticated(root,*args)
            with mock.patch.object(frozen,"git_text",side_effect=fake):
                with self.assertRaises(frozen.GuardError):
                    successor.check_checkout_identity(Path("."),H)
        def false_tree(root,*args):
            if args==("rev-parse","HEAD^{tree}"):
                return "f"*40
            return authenticated(root,*args)
        with mock.patch.object(frozen,"git_text",side_effect=false_tree):
            with self.assertRaises(frozen.GuardError):
                successor.check_checkout_identity(Path("."),H)

    def test_original_historical_a2_test_git_identity_is_not_assumed(self):
        self.assertEqual(successor.HISTORICAL_A2_INTRODUCER,
                         "f71a76032b169aac7bfe0694aa715339a94d4e05")
        self.assertEqual(successor.LATE_A2_TEST_ORIGINAL_BLOB,
                         "c0f49038ea9b590720c78be85968eb63f5ac820f")
        self.assertNotEqual(successor.LATE_A2_TEST_ORIGINAL_BLOB,
                            successor.LATE_A2_TEST_PROPOSED_BLOB)

    def test_history_cannot_change_toolchain_or_proofs(self):
        old,current=fixture()
        for key in ("lean-toolchain","lake-manifest.json",
                    *frozen.ACCEPTED_A2_PROOF_BLOBS):
            altered=dict(current)
            altered[key]=("100644","0"*40)
            with self.subTest(key=key),self.assertRaises(frozen.GuardError):
                successor.reconcile(old,altered)


    @staticmethod
    def _git_raw(root, *args):
        return subprocess.check_output(
            ["git", *args], cwd=root, stderr=subprocess.DEVNULL, timeout=35)

    @staticmethod
    def _blob_oid(raw):
        return hashlib.sha1(
            b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw
        ).hexdigest()

    def _historically_anchored_virtual_tree(self):
        """Build proposed 30-source truth from ACTUAL Git objects, not mocks."""
        root=Path(__file__).resolve().parents[2]
        git=self._git_raw
        checked=git(root,"rev-parse","HEAD").decode().strip()
        self.assertRegex(checked,r"^[a-f0-9]{40}$")
        for anchor in (frozen.BASE,successor.HISTORICAL_A2_INTRODUCER,
                       workflow_profile.PREACTIVATION_HEAD):
            self.assertEqual(subprocess.run(
                ["git","merge-base","--is-ancestor",anchor,checked],
                cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,
                timeout=35).returncode,0,
                "actual historical baseline missing from exact Git history")
        baseline=frozen.parse_tree(
            git(root,"ls-tree","-r","-z",frozen.BASE))
        current=frozen.parse_tree(
            git(root,"ls-tree","-r","-z","HEAD"))
        old25=frozen.parse_tree(
            git(root,"ls-tree","-r","-z",workflow_profile.PREACTIVATION_HEAD))
        self.assertEqual(git(root,"rev-parse",frozen.BASE+"^{tree}").decode().strip(),
                         frozen.BASE_TREE)
        self.assertNotIn(successor.LATE_A2_TEST,baseline)
        self.assertEqual(git(root,"rev-parse",
                             successor.HISTORICAL_A2_INTRODUCER+":"+
                             successor.LATE_A2_TEST).decode().strip(),
                         successor.LATE_A2_TEST_ORIGINAL_BLOB)
        phase,report=workflow_profile.audited_source_phase(root,checked)
        self.assertEqual(current[successor.LATE_A2_TEST],
                         ("100644",successor.LATE_A2_TEST_ORIGINAL_BLOB
                          if phase=="staged" else
                          successor.LATE_A2_TEST_PROPOSED_BLOB))
        def committed_json(path):
            return json.loads(git(root,"show",checked+":"+path))
        full=committed_json(workflow_profile.FULL_MANIFEST)
        contract=committed_json(workflow_profile.CONTRACT_MANIFEST)
        suite=committed_json(workflow_profile.STAGE+"test_workflow_v2_manifest.json")
        historical=committed_json(workflow_profile.STAGE+"manifest.json")
        additions=committed_json(workflow_profile.PROPOSAL_MANIFEST)
        self.assertEqual(report["historical_original_workflow_count"],25)
        self.assertEqual(report["current_reviewed_workflow_count"],30)
        self.assertEqual(report["retained_historical_count"],23)
        self.assertFalse(report["independent_security_review"])
        self.assertFalse(report["owner_activation_authorized"])
        for manifest in (full,contract,suite,historical,additions):
            for claim in ("independent_security_review","owner_activation_authorized",
                          "mathematical_acceptance","publication_authorized"):
                if claim in manifest:
                    self.assertIs(manifest[claim],False,
                                  "candidate manifest cannot grant "+claim)
        replacements={r["target"]:r for r in full["full_replacements"]}
        self.assertEqual(set(replacements),{
            ".github/workflows/research-lean.yml",
            ".github/workflows/research-integrity.yml",
        })
        self.assertEqual(len(contract["expected_workflow_git_blobs"]),30)
        self.assertEqual(len(successor.PINNED_MODIFIED_PROVIDERS),12)
        intended={}
        future=dict(current)
        def stage_oid(path,recorded):
            raw=git(root,"show",checked+":"+path)
            git_oid=git(root,"rev-parse",checked+":"+path).decode().strip()
            self.assertEqual(git_oid,self._blob_oid(raw),
                             "actual Git object bytes do not match object ID")
            self.assertEqual(git_oid,recorded,
                             "staged manifest is not an authority over Git")
            return git_oid
        for path,stored_pin in successor.PINNED_MODIFIED_PROVIDERS.items():
            self.assertIn(path,baseline,"only existing PR79 providers can be modified")
            self.assertIn(path,old25,"original 25-history snapshot lost a provider")
            if path in replacements:
                stage=replacements[path]
                name=path.removeprefix(".github/workflows/")
                expected=stage_oid(stage["staged_source"],stage["git_blob_oid"])
                self.assertEqual(expected,contract["expected_workflow_git_blobs"][name])
                if phase=="staged":
                    self.assertEqual(current[path],old25[path],
                        "original required workflow changed before activation")
                else:
                    self.assertEqual(current[path],("100644",expected),
                        "installed required workflow differs from reviewed staged blob")
                future[path]=("100644",expected)
            elif path=="verification/integrity/workflow_contract.py":
                expected=stage_oid(contract["staged_source"],
                                   contract["staged_git_blob_oid"])
                if phase=="active":
                    self.assertEqual(current[path],("100644",expected))
                future[path]=("100644",expected)
            elif path=="verification/integrity/tests/test_workflow.py":
                expected=stage_oid(suite["staged_test_source"],
                                   suite["staged_test_blob_oid"])
                if phase=="active":
                    self.assertEqual(current[path],("100644",expected))
                future[path]=("100644",expected)
            else:
                expected=current[path][1]
                self.assertEqual(old25[path],current[path],
                                 "retained source changed since 25-workflow anchor")
                if path.startswith(".github/workflows/"):
                    name=path.removeprefix(".github/workflows/")
                    self.assertEqual(expected,
                        contract["expected_workflow_git_blobs"][name])
                raw=git(root,"show",checked+":"+path)
                self.assertEqual(self._blob_oid(raw),expected)
            self.assertEqual(stored_pin,expected,
                             "A2 successor has stale provider pin: "+path)
            intended[path]=expected
        self.assertEqual(set(intended),set(successor.PINNED_MODIFIED_PROVIDERS))
        late=next(r for r in historical["staged_replacements"]
                  if r["target"]==successor.LATE_A2_TEST)
        self.assertEqual(stage_oid(late["source"],late["git_blob_oid"]),
                         successor.LATE_A2_TEST_PROPOSED_BLOB)
        future[successor.LATE_A2_TEST]=(
            "100644",successor.LATE_A2_TEST_PROPOSED_BLOB)
        if phase=="active":
            self.assertEqual(current[successor.LATE_A2_TEST],
                             future[successor.LATE_A2_TEST])
        for added in additions["proposals"]:
            path=added["workflow_path"]
            oid=stage_oid(added["staged_source_path"],added["git_blob_oid"])
            if phase=="staged":
                self.assertNotIn(path,current)
            else:
                self.assertEqual(current.get(path),("100644",oid),
                                 "installed proposed workflow blob differs from stage")
            self.assertNotIn(path,baseline)
            future[path]=("100644",oid)
        for path,oid in frozen.ACCEPTED_A2_PROOF_BLOBS.items():
            self.assertEqual(current[path],("100644",oid),
                             "accepted mathematical source blob was changed")
        for path in ("lean-toolchain","lake-manifest.json"):
            self.assertEqual(current[path],baseline[path],
                             "historical Lean/toolchain dependency identity changed")
        self.assertEqual(len([p for p in future
            if p.startswith(".github/workflows/") and p.endswith((".yml",".yaml"))]),
            30)
        if phase=="active":
            self.assertEqual(current,future,
                "actual active 30-tree differs from reviewed virtual 30-tree")
        audited=successor.reconcile(baseline,future)
        self.assertEqual(len(audited["pinned_successor_provider_paths"]),12)
        return root,checked,baseline,future,full,contract

    def test_all_twelve_actual_git_provider_pins_match_staged_manifests(self):
        self._historically_anchored_virtual_tree()

    def test_each_stale_a2_pin_and_staged_source_substitution_fail_closed(self):
        root,checked,baseline,future,full,contract=(
            self._historically_anchored_virtual_tree())
        phase=workflow_profile.source_phase(root,checked)
        for path in (".github/workflows/research-integrity.yml",
                     ".github/workflows/research-lean.yml",
                     "verification/integrity/workflow_contract.py"):
            with self.subTest(forged_pin=path),mock.patch.dict(
                    successor.PINNED_MODIFIED_PROVIDERS,{path:"0"*40}):
                with self.assertRaises(frozen.GuardError):
                    successor.reconcile(baseline,future)
        for path in (".github/workflows/research-integrity.yml",
                     ".github/workflows/research-lean.yml"):
            altered=dict(future)
            altered[path]=("100644","0"*40)
            with self.subTest(forged_candidate=path),self.assertRaises(
                    frozen.GuardError):
                successor.reconcile(baseline,altered)
        stage_paths=[contract["staged_source"]]
        stage_paths += [r["staged_source"] for r in full["full_replacements"]]
        true_git=workflow_profile.git
        def committed_json(r,head,path):
            return json.loads(true_git(r,"show",head+":"+path))
        for staged in stage_paths:
            raw=true_git(root,"show",checked+":"+staged)
            forged=raw+b"\n# changed and misleadingly rehashed\n"
            spoofed_oid=self._blob_oid(forged)
            def forged_git(r,*args):
                if args==("show",checked+":"+staged):
                    return forged
                return true_git(r,*args)
            def forged_manifest(r,head,path):
                data=committed_json(r,head,path)
                if staged==workflow_profile.CONTRACT and path==(
                        workflow_profile.CONTRACT_MANIFEST):
                    data["staged_git_blob_oid"]=spoofed_oid
                if path==workflow_profile.FULL_MANIFEST:
                    for row in data["full_replacements"]:
                        if row["staged_source"]==staged:
                            row["git_blob_oid"]=spoofed_oid
                return data
            with self.subTest(forged_stage=staged),\
                 mock.patch.object(workflow_profile,"git",
                                   side_effect=forged_git),\
                 mock.patch.object(workflow_profile,"_json",
                                   side_effect=forged_manifest),\
                 self.assertRaises(workflow_profile.ToolingMigrationError):
                workflow_profile.audit(root,checked,phase=phase)

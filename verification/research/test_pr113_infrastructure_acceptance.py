"""Synthetic infrastructure gate negatives. Never a real approval."""
from __future__ import annotations

import io
import json
import unittest
from unittest import mock
import zipfile

import infrastructure_acceptance as infra
import release_target


H = "a" * 40


def zipped(files):
    dest = io.BytesIO()
    with zipfile.ZipFile(dest, "w", zipfile.ZIP_DEFLATED) as z:
        for name, data in sorted(files.items()):
            z.writestr(name, data)
    return dest.getvalue()


def historical_files():
    old = {
        "format": "Permansson.Hardening.Check.v1",
        "context": {}, "status": "PASS", "check": "archive-reproducibility",
        "details": {
            "acceptance_scope": "accepted_artifact_replay_only",
            "isolation": {"network_isolation": "ENFORCED",
                          "capabilities": "all_zero"}
        }
    }
    current = {
        "format": "Permansson.Hardening.Tests.v1",
        "schema_version": 1, "status": "PASS", "suite": "workflow",
        "context":{"repository":"HMarcusWH/PermanssonLean",
                   "checked_sha":H,"checked_tree":"9"*40,"event":"local"},
        "execution_tracked_clean": True, "methods_run": 5,
        "failures": 0, "errors": 0, "skips": 0,
        "covered_requirements": ["CI-06","CI-07"]
    }
    obj = lambda x: (json.dumps(x, sort_keys=True) + "\n").encode()
    oldraw, newraw = obj(old), obj(current)
    receipt = {
        "status": "DUAL_T_AND_H_EXECUTED_UNREVIEWED",
        "original_T_archive_unchanged": True,
        "historical_T": release_target.T, "current_H": H,
        "historical_T_report_sha256": infra.sha(oldraw),
        "current_H_report_sha256": infra.sha(newraw),
        "independent_security_review": False,
        "versioned_successor_T2_approved": False,
    }
    dossier = {
        "format": "Permansson.PR113.ToolingSecurityReviewDossier.v1",
        "status": "COMPLETE_DUAL_EXECUTION_CANDIDATE_SECURITY_REVIEW_PENDING",
        "T": release_target.T, "H": H,
        "T_original_offline_restore_report_sha256": infra.sha(oldraw),
        "H_original_workflow_test_report_sha256": infra.sha(newraw),
        "legacy_T_did_not_accept_current_C": True,
        "owner_authorization_present": False,
        "independent_security_review_present": False,
        "historical_required_CI_replaced": False,
        "required_workflow_inventory_count": 25,
    }
    return {
        "original_T_archive.json": oldraw,
        "current_H_workflow.json": newraw,
        "dual_tooling_unreviewed.json": obj(receipt),
        "T2_security_review_candidate.json": obj(dossier),
    }


def compiler(prefix, status, mutation_names):
    commands = []
    content = {}
    for n, label in enumerate(
            ["compiler_version", "research_build", "signatures_axioms",
             "positive_fixture", *mutation_names, "source_1", "source_2"], 1):
        bad = label in mutation_names
        text = b"error: type mismatch on false theorem\n" if bad else b"proof okay\n"
        logfile = f"{n:02}_{label}.log"
        content[f"{prefix}/{logfile}"] = text
        commands.append({
            "label": label, "returncode": 1 if bad else 0,
            "log": logfile, "log_sha256": infra.sha(text),
        })
    row = {
        "status": status, "source_unchanged": True,
        "declarations": {"Some.target": ["propext"]},
        "mutations": {name: {"status": "SEMANTICALLY_REJECTED"}
                      for name in mutation_names},
        "commands": commands,
        "artifacts": {
            item.removeprefix(prefix + "/"): {
                "bytes": len(raw), "sha256": infra.sha(raw)}
            for item, raw in content.items()
        },
    }
    content[f"{prefix}/receipt.json"] = (
        json.dumps(row, sort_keys=True) + "\n").encode()
    return content


def synthetic_lake_manifest():
    return {
        "packagesDir": ".lake/packages",
        "packages": [
            {"type": "git", "name": "mathlib",
             "rev": "5ed2965256430c3649e86755f9576b54eca72435"},
            {"type": "git", "name": "aesop", "rev": "1"*40},
        ],
    }


def fake_bridge():
    manifest = synthetic_lake_manifest()
    raw = json.dumps(manifest, sort_keys=True).encode()
    return {
        "format": "Permansson.PR113.HistoricalA2DependencyBridge.v1",
        "status": "PINNED_DEPENDENCIES_REUSED_WITHOUT_PROOF_BUILD_IMPORT",
        "historical_head": infra.A2_HISTORICAL,
        "current_head": H,
        "manifest_sha256": infra.sha(raw),
        "pinned_packages": {p["name"]:p["rev"] for p in manifest["packages"]},
        "original_verifier_modified": False,
        "historical_project_proofs_reused": False,
        "independent_security_review": False,
        "mathematical_acceptance": False,
    }


def a2_files():
    left = compiler(
        "historical_original_A2",
        "LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING",
        infra.HISTORICAL_MUTATIONS)
    right = compiler(
        "pr113_successor_A2",
        "SUCCESSOR_KERNEL_CHECKED_REVIEW_PENDING",
        infra.SUCCESSOR_MUTATIONS)
    historical_receipt = left["historical_original_A2/receipt.json"]
    overall = {
        "format": "Permansson.PR113.DualA2CompilerCandidate.v2",
        "status": "BOTH_ACTUAL_A2_COMPILER_PATHS_EXECUTED_UNREVIEWED",
        "historical_source_commit": infra.A2_HISTORICAL,
        "current_source_commit": H, "historical_test_executed": True,
        "successor_test_executed": True,
        "historical_semantic_mutants": 4, "successor_semantic_mutants": 4,
        "original_verifier_modified": False,
        "independent_security_approval": False,
        "independent_mathematical_approval": False,
        "merged_main_sha": None, "full_release_approved": False,
        "historical_runtime_provenance": {
            "imported_current_A2_gate": False,
            "historical_checkout_sha": infra.A2_HISTORICAL,
            "output_receipt_sha256": infra.sha(historical_receipt),
        },
    }
    return {
        "historical_dependency_bridge.json":
            (json.dumps(fake_bridge(), sort_keys=True)+"\n").encode(),
        **left, **right, "unreviewed_dual_A2_candidate.json":
            (json.dumps(overall, sort_keys=True) + "\n").encode(),
    }


class HistoricalEvidenceTests(unittest.TestCase):
    def test_T_reports_original_actual_bytes(self):
        files = historical_files()
        self.assertEqual(
            infra.inspect_T(files, H)["T_report_sha256"],
            infra.sha(files["original_T_archive.json"]))
        files["current_H_workflow.json"] = b'{"status":"PASS"}'
        with self.assertRaises(infra.InfrastructureError):
            infra.inspect_T(files, H)

    def test_A2_has_4_meaningful_mutants_on_both_original_versions(self):
        files = a2_files()
        self.assertEqual(
            infra.inspect_A2(files, H)["original_A2_sha256"],
            infra.sha(files["historical_original_A2/receipt.json"]))
        original = json.loads(files["historical_original_A2/receipt.json"])
        original["mutations"].pop(next(iter(original["mutations"])))
        files["historical_original_A2/receipt.json"] = json.dumps(original).encode()
        with self.assertRaises(infra.InfrastructureError):
            infra.inspect_A2(files, H)

    def test_borrowed_logged_mutant_or_parser_failure_cannot_count(self):
        files = a2_files()
        key = next(k for k in files if k.startswith(
            "pr113_successor_A2/") and "omit_baseline_reporting_error.log" in k)
        files[key] = b"error: parser error\n"
        with self.assertRaises(infra.InfrastructureError):
            infra.inspect_A2(files, H)

    def test_reviewed_workflow_hash_includes_exact_git_bytes(self):
        source=(b"# Review-pending source-controlled historical verification\n"
                b"historical-T-and-H-unreviewed\n"
                b"historical-A2-and-H-unreviewed\n")
        with mock.patch.object(infra.subprocess,"check_output",
                               return_value=source):
            raw=infra.exact_committed_blob(
                H,infra.ACTIVE_WORKFLOW,git=infra.real_git)
        self.assertEqual(raw,source)
        self.assertNotEqual(infra.sha(raw),infra.sha(raw.strip()))
        self.assertEqual(infra.exact_committed_blob(
            H,infra.ACTIVE_WORKFLOW,git=lambda *a:source),source)


    def test_lake_manifest_full_committed_bytes_never_trimmed(self):
        raw=b'{"packagesDir":".lake/packages"}\n'
        with mock.patch.object(infra.subprocess,"check_output",
                               return_value=raw) as checked:
            self.assertEqual(infra.exact_committed_lake_blob(
                H,git=infra.real_git),raw)
            self.assertEqual(checked.call_args.args[0],
                             ["git","show",H+":lake-manifest.json"])
        self.assertEqual(infra.exact_committed_lake_blob(
            H,git=lambda *a:raw.decode("utf-8")),raw)
        self.assertNotEqual(infra.sha(raw),infra.sha(raw.strip()))


    def test_historical_dependency_bridge_rejects_forgery(self):
        files = a2_files()
        manifest=json.dumps(synthetic_lake_manifest(), sort_keys=True).encode()
        evidence=infra.verify_A2_dependency_bridge(files,H,manifest_raw=manifest)
        self.assertEqual(evidence,infra.sha(
            files["historical_dependency_bridge.json"]))
        for mutation in (
            lambda x: x.update(current_head="b"*40),
            lambda x: x.update(manifest_sha256="0"*64),
            lambda x: x.update(pinned_packages={"mathlib":"0"*40}),
            lambda x: x.update(historical_project_proofs_reused=True),
            lambda x: x.update(independent_security_review=True),
            lambda x: x.update(original_verifier_modified=True),
        ):
            with self.subTest(mutation=mutation):
                modified=a2_files()
                obj=json.loads(modified["historical_dependency_bridge.json"])
                mutation(obj)
                modified["historical_dependency_bridge.json"] = (
                    json.dumps(obj, sort_keys=True)+"\n").encode()
                with self.assertRaises(infra.InfrastructureError):
                    infra.verify_A2_dependency_bridge(
                        modified,H,manifest_raw=manifest)
        with self.assertRaises(infra.InfrastructureError):
            infra.verify_A2_dependency_bridge(
                a2_files(),H,manifest_raw=b"{}")


    def test_safe_zip_member_bounds(self):
        raw = zipped(historical_files())
        self.assertIn("original_T_archive.json", infra.inspect_zip(raw))
        for bad in ("../T2.json", "bad\\path", "X/../../evil",
                    "folder/.", "bad/link/../../../f.txt"):
            with self.subTest(bad=bad):
                with self.assertRaises(infra.InfrastructureError):
                    infra.inspect_zip(zipped({bad: b"bad"}))

    def test_bare_status_fails_when_actual_original_reports_absent(self):
        files = {"dual_tooling_unreviewed.json": b'{"status":"PASS"}'}
        with self.assertRaises(infra.InfrastructureError):
            infra.inspect_T(files, H)
        with self.assertRaises(infra.InfrastructureError):
            infra.inspect_A2(files, H)


class SourceArtifactTests(unittest.TestCase):
    def evidence(self, *, kind="T"):
        job, artifact_name = infra.EXPECTED_ARTIFACTS[kind]
        payload = zipped(historical_files() if kind == "T" else a2_files())
        ids = dict(run_id=101, run_attempt=2, job_id=102,
                   check_run_id=103, artifact_id=104)
        api = {
            "/actions/runs/101": {
                "id": 101, "head_sha": H,
                "head_branch": "research/final-mathematical-closure",
                "event": "push", "status": "completed", "conclusion": "success",
                "run_attempt": 2,
                "path": infra.ACTIVE_WORKFLOW
            },
            "/actions/runs/101/jobs?per_page=100": {
                "jobs": [{
                    "id": 102, "run_id": 101, "run_attempt": 2,
                    "head_sha": H, "name": job, "status": "completed",
                    "conclusion": "success",
                    "check_run_url": "https://api.github.com/check-runs/103",
                    "started_at": "2026-10-25T00:00:00Z",
                    "completed_at": "2026-10-25T00:15:00Z",
                }]
            },
            "/check-runs/103": {
                "id": 103, "head_sha": H, "name": job,
                "status": "completed", "conclusion": "success",
                "app": {"slug": "github-actions"}
            },
            "/actions/artifacts/104": {
                "id": 104, "name": artifact_name, "expired": False,
                "digest": "sha256:" + infra.sha(payload),
                "created_at": "2026-10-25T00:10:00Z",
                "workflow_run": {"id": 101, "head_sha": H}
            }
        }
        return ids, payload, api

    def test_genuine_green_job_artifact_bytes_authenticated(self):
        ids, raw, api = self.evidence()
        item = infra.authenticate_original_zip(
            "T", ids, raw, H, live=api.__getitem__)
        self.assertEqual(item["sha256"], infra.sha(raw))

    def test_failed_job_even_with_real_uploaded_zip_is_blocked(self):
        ids, raw, api = self.evidence()
        api["/actions/runs/101/jobs?per_page=100"]["jobs"][0][
            "conclusion"] = "failure"
        with self.assertRaises(infra.InfrastructureError):
            infra.authenticate_original_zip(
                "T", ids, raw, H, live=api.__getitem__)

    def test_foreign_head_attempt_artifact_and_missing_identity_block(self):
        for edit in (
            lambda a: a["/actions/runs/101"].update(head_sha="b"*40),
            lambda a: a["/actions/runs/101"].update(run_attempt=1),
            lambda a: a["/actions/artifacts/104"].update(digest="sha256:"+"0"*64),
            lambda a: a["/actions/artifacts/104"].update(expired=True),
        ):
            with self.subTest(edit=edit):
                ids, raw, api = self.evidence()
                edit(api)
                with self.assertRaises(infra.InfrastructureError):
                    infra.authenticate_original_zip(
                        "T", ids, raw, H, live=api.__getitem__)
        ids, raw, api = self.evidence()
        ids["approval"] = True
        with self.assertRaises(infra.InfrastructureError):
            infra.authenticate_original_zip("T", ids, raw, H, live=api.__getitem__)


class IndependentReviewTests(unittest.TestCase):
    def record(self):
        attested = {
            "head_sha": H,
            "workflow_sha256": "0"*64,
            "T_artifact_sha256": "1"*64,
            "A2_artifact_sha256": "2"*64,
            "original_base_sha": release_target.B113,
        }
        approved = {
            "id": 987, "state": "APPROVED", "commit_id": H,
            "submitted_at": "2026-10-25T00:20:00Z",
            "user": {"login": "trusted-security-reviewer"},
            "body": infra.REVIEW_PREFIX + json.dumps(attested),
        }
        policy = {"reviewers": [
            {"login": "trusted-security-reviewer", "approved_by": "HMarcusWH",
             "independence_disclosed": True}]}
        return approved, policy, attested

    def test_real_independent_attestation_only_and_no_fake_approvals(self):
        review, policy, payload = self.record()
        self.assertTrue(infra.approved_security_review(
            987, "HMarcusWH", H, payload, policy,
            paginate=lambda p: [review]))
        changed = dict(payload, T_artifact_sha256="f"*64)
        with self.assertRaises(infra.InfrastructureError):
            infra.approved_security_review(
                987, "HMarcusWH", H, changed, policy,
                paginate=lambda p: [review])

    def test_no_owner_self_review_or_later_changes_requested(self):
        review, policy, payload = self.record()
        review["user"]["login"] = "HMarcusWH"
        with self.assertRaises(infra.InfrastructureError):
            infra.approved_security_review(
                987, "HMarcusWH", H, payload, policy,
                paginate=lambda p: [review])
        review, policy, payload = self.record()
        revoked = dict(review, id=988, state="CHANGES_REQUESTED",
                       submitted_at="2026-10-25T00:22:00Z")
        with self.assertRaises(infra.InfrastructureError):
            infra.approved_security_review(
                987, "HMarcusWH", H, payload, policy,
                paginate=lambda p: [review, revoked])


class SeparateGateTests(unittest.TestCase):
    def test_cannot_promote_infrastructure_receipt_to_mathematical_release(self):
        from final_closure_schema import validate_overlay
        candidate = {
            "format": "Permansson.PR113.InfrastructureAcceptanceReceipt.v1",
            "status": "INFRASTRUCTURE_READY_FOR_SEPARATE_OWNER_MERGE_DECISION",
            "independent_mathematical_review": False,
            "publication_authorized": False,
        }
        with self.assertRaises(Exception):
            validate_overlay(candidate)


    def test_full_infrastructure_graph_synthetic_positive_never_math_release(self):
        from test_pr113_release_target import fake_intent, fake_apis, fake_target
        tzip, azip = zipped(historical_files()), zipped(a2_files())
        source_test = SourceArtifactTests()
        tids, _, tapi = source_test.evidence(kind="T")
        aids, _, aapi = source_test.evidence(kind="A2")
        # The two original artifacts belong to two successful, separate jobs.
        newids = {
            "run_id": 201, "run_attempt": 2, "job_id": 202,
            "check_run_id": 203, "artifact_id": 204,
        }
        aid_api = {
            key.replace("101", "201").replace("102", "202")
               .replace("103", "203").replace("104", "204"): value
            for key, value in aapi.items()
        }
        # Fix the authenticated identity fields, not merely the URL keys.
        arun = aid_api["/actions/runs/201"]
        arun["id"] = 201
        job = aid_api["/actions/runs/201/jobs?per_page=100"]["jobs"][0]
        job.update(id=202, run_id=201,
                   check_run_url="https://api.github.com/check-runs/203")
        checked = aid_api["/check-runs/203"]
        checked["id"] = 203
        art = aid_api["/actions/artifacts/204"]
        art.update(id=204, digest="sha256:"+infra.sha(azip))
        art["workflow_run"].update(id=201)
        tapi["/actions/artifacts/104"]["digest"] = "sha256:"+infra.sha(tzip)
        api = {**tapi, **aid_api}
        # Both distinct real-API shapes use the staged workflow identity.
        for key in ("/actions/runs/101", "/actions/runs/201"):
            api[key]["path"] = infra.ACTIVE_WORKFLOW
        target_gh, target_git, t_api = fake_apis()
        api.update(t_api)
        workflow = ("# Review-pending source-controlled historical verification\n"
                    "name: PR113 Historical T and A2 candidates\n"
                    "jobs:\n  historical-T-and-H-unreviewed:\n"
                    "  historical-A2-and-H-unreviewed:\n")
        policy = {
            "format": "Permansson.InfrastructureReviewerAuthority.v1",
            "owner": "HMarcusWH",
            "status": "OWNER_AUTHORIZED",
            "reviewers": [
                {"login":"external-security-reviewer",
                 "independence_disclosed":True,
                 "approved_by":"HMarcusWH"}]
        }
        def git(*args):
            if args == ("show", H + ":" + infra.AUTHORITY_PATH):
                return json.dumps(policy)
            if args == ("show", H + ":" + infra.ACTIVE_WORKFLOW):
                return workflow
            if args == ("show", H + ":lake-manifest.json"):
                return json.dumps(synthetic_lake_manifest(), sort_keys=True)
            if args == ("show", H + ":" + release_target.INTENT_PATH):
                return json.dumps(fake_intent())
            return target_git(*args)
        checks = {name:{"id":n,"head_sha":H,"name":name}
                  for n,name in enumerate(sorted(infra.REQUIRED),1)}
        receipt = {
            "format":infra.FORMAT, "target":fake_target(),
            "source_bound_ci":[{"name":name,"id":check["id"],
                                "head_sha":H}
                                for name,check in checks.items()],
            "historical_T":tids, "historical_A2":newids,
            "security_review_id":789,
        }
        attestation = {
            "head_sha": H, "workflow_sha256": infra.sha(workflow.encode()),
            "T_artifact_sha256": infra.sha(tzip),
            "A2_artifact_sha256": infra.sha(azip),
            "original_base_sha": release_target.B113,
        }
        approved_review = {
            "id":789, "state":"APPROVED","commit_id":H,
            "submitted_at":"2026-10-25T00:25:00Z",
            "user":{"login":"external-security-reviewer"},
            "body":infra.REVIEW_PREFIX + json.dumps(attestation),
        }
        api["/pulls/113"]["user"]={"login":"HMarcusWH"}
        with mock.patch.object(infra.release_target,"exact_intent",
                               wraps=infra.release_target.exact_intent):
            verified = infra.check_evidence(
                receipt,tzip,azip,git=git,live=api.__getitem__,
                checks=lambda h: checks,
                paginate=lambda path:[approved_review])
        self.assertEqual(verified["required_ci_successful"],12)
        self.assertEqual(
            verified["status"],
            "INFRASTRUCTURE_READY_FOR_SEPARATE_OWNER_MERGE_DECISION")
        self.assertFalse(verified["independent_mathematical_review"])
        self.assertFalse(verified["publication_authorized"])
        self.assertFalse(verified["merge_authorized"])

    def test_historical_required_gate_cannot_self_require_ci_or_approve_merge(self):
        from test_pr113_release_target import fake_target
        payload = {
            "format": infra.FORMAT, "target": fake_target(),
            "source_bound_ci": [], "historical_T":{},
            "historical_A2":{}, "security_review_id":987,
        }
        report_target = {"head_sha": H,"phase":"infrastructure_premerge",
                         "synthetic_sha":"b"*40}
        with mock.patch.object(infra.release_target,"candidate_bindings"), \
             mock.patch.object(infra.release_target,"exact_intent",
                               return_value={}), \
             mock.patch.object(infra.release_target,"bind",
                               return_value=report_target), \
             mock.patch.object(infra,"authenticate_original_zip",
                               side_effect=lambda kind,*args,**kw:
                                   {"sha256":("1" if kind=="T" else "2")*64}), \
             mock.patch.object(infra,"inspect_zip",return_value={}), \
             mock.patch.object(infra,"inspect_T",return_value={"T":"PASS"}), \
             mock.patch.object(infra,"inspect_A2",return_value={"A2":"PASS"}), \
             mock.patch.object(infra,"verify_A2_dependency_bridge",
                               return_value="3"*64), \
             mock.patch.object(infra,"authority_policy",
                               return_value={"status":"OWNER_AUTHORIZED"}), \
             mock.patch.object(infra,"approved_security_review",
                               return_value=True), \
             mock.patch.object(infra,"authenticated_checks",
                               side_effect=AssertionError("self-dependent CI")):
            def git(*args):
                if args[0]=="show" and args[1].endswith(infra.ACTIVE_WORKFLOW):
                    return ("# Review-pending source-controlled historical verifier\n"
                            "historical-T-and-H-unreviewed\n"
                            "historical-A2-and-H-unreviewed\n")
                if args[0]=="show" and args[1].endswith("lake-manifest.json"):
                    return "{}"
                raise AssertionError(args)
            def live(path):
                if path=="/pulls/113":
                    return {"user":{"login":"HMarcusWH"}}
                raise AssertionError(path)
            receipt=infra.check_historical_only(
                payload,b"original-T",b"original-A2",
                git=git,live=live,paginate=lambda p:[])
            self.assertEqual(receipt["required_ci_successful"],0)
            self.assertIn("HISTORICAL_T_AND_A2",receipt["status"])
            self.assertFalse(receipt["independent_mathematical_review"])
            self.assertFalse(receipt["merge_authorized"])
            self.assertFalse(receipt["publication_authorized"])
            with self.assertRaises(infra.InfrastructureError):
                infra.check_evidence(payload,b"original-T",b"original-A2",
                                     git=git,live=live,checks=lambda h: {},
                                     paginate=lambda p:[])

    def test_all_12_exact_source_checks_required_and_missing_review_blocks(self):
        good = {
            "format": infra.FORMAT,
            "target": {"head_sha": H},
            "source_bound_ci": [],
            "historical_T": {},
            "historical_A2": {},
            "security_review_id": 0,
        }
        # All invalid external targets are rejected before any Git, GitHub
        # or required-CI lookup, even when their head SHA looks syntactically
        # valid. No fake aaaa... Git object should be requested.
        with mock.patch.object(infra, "real_git",
                               side_effect=AssertionError("Git lookup")) as git, \
             mock.patch.object(infra, "real_live",
                               side_effect=AssertionError("GitHub lookup")) as live, \
             mock.patch.object(infra, "authenticated_checks",
                               side_effect=AssertionError("CI lookup")) as checks:
            with self.assertRaises(release_target.TargetError):
                infra.check_evidence(good, b"x", b"y",
                                     git=git, live=live, checks=checks)
            git.assert_not_called()
            live.assert_not_called()
            checks.assert_not_called()


if __name__ == "__main__":
    unittest.main()

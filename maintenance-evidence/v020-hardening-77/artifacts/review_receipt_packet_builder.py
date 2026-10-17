"""Disposable curation controls; never assembles or approves a final packet."""
from argparse import ArgumentParser, Namespace
from copy import deepcopy
import io
import json
from pathlib import Path
import tempfile
import zipfile

import build_maintenance_receipt_packet as m


def run(artifacts, scratch):
    checks = []
    def rejected(name, callback, expected):
        try:
            callback()
        except ValueError as error:
            if expected not in str(error):
                raise
        else:
            raise ValueError("Negative control accepted: " + name)
        checks.append({"case": name, "status": "PASS", "expected_rejection": expected})
    selected = {}
    for index, (count, digest) in m.HISTORICAL_INDICES.items():
        for path, data in m.indexed_inputs(artifacts, index, count, digest).items():
            if path in selected and selected[path] != data:
                raise ValueError("Historical overlap mismatch")
            selected[path] = data
        checks.append({"case": "pinned_index_" + index, "status": "PASS", "payload_count": count})
    for name in m.REQUIRED_FILES:
        selected[name] = m.read(artifacts, name)
    for name, data in selected.items():
        m.screen_payload(data, name)
    checks.append({"case": "explicit_historical_and_required_privacy_screen", "status": "PASS", "files": len(selected)})
    for bad in ("../private.json", "/absolute.json", "x\\y.json", "C:/private.json", "x\ny.json"):
        rejected("unsafe_path", lambda bad=bad: m.relative(bad), "relative path")
    # Construct inert fixture URLs at runtime; no actual credential is used.
    url = "https://" + "example.invalid/a?" + "sig=fixture"
    rejected("signed_url_text", lambda: m.screen_payload(url.encode(), "test.txt"), "signed/credential URL")
    escaped = json.dumps({"url": url}).replace("/", "\\/").encode()
    rejected("signed_url_JSON_escape", lambda: m.screen_payload(escaped, "test.json"), "signed/credential URL")
    container = io.BytesIO()
    with zipfile.ZipFile(container, "w") as archive:
        archive.writestr("text.csv", url)
    rejected("signed_url_arbitrary_ZIP_member", lambda: m.screen_payload(container.getvalue(), "fixture.zip"), "signed/credential URL")
    with tempfile.TemporaryDirectory(prefix="receipt-builder-controls-", dir=scratch) as temporary:
        root = Path(temporary)
        (root / "capture").mkdir()
        (root / "capture/private-report.json").write_bytes(b"{}")
        (root / "capture/index.json").write_bytes(m.json_bytes({"files": [
            {"path": "private-report.json", "size": 2, "sha256": m.sha(b"{}")}] }))
        rejected("unapproved_final_member", lambda: m.indexed_inputs(root, "capture/index.json", final=True), "explicit whitelist review")
        tiny = io.BytesIO()
        with zipfile.ZipFile(tiny, "w") as archive:
            archive.writestr("context.json", b"{}")
        payload = tiny.getvalue()
        source = "hardening-pr77-repaired-acceptance/a.zip"
        mapping = {source: "artifacts/" + source}
        files = {mapping[source]: payload}
        ledger = {"entry": {"original_artifact_path": source, "path": "old-layout",
            "member": "context.json", "sha256": m.sha(payload), "bytes": len(payload),
            "member_sha256": m.sha(b"{}"), "member_bytes": 2}}
        portable, links = m.portable_ledger(ledger, mapping, artifacts, "ledger/acceptance-ledger.json")
        m.verify_links(links, files)
        if ledger["entry"]["path"] != "old-layout" or portable["entry"]["path"] != "../artifacts/" + source:
            raise ValueError("Raw/portable ledger mutation error")
        checks.append({"case": "portable_links_preserve_raw_and_verify_member", "status": "PASS"})
        altered = deepcopy(links)
        altered[0]["expected_member_sha256"] = "0" * 64
        rejected("wrong_member_digest", lambda: m.verify_links(altered, files), "member digest differs")
        head, base, synthetic, tooling = "1" * 40, "2" * 40, "3" * 40, "4" * 40
        cases = []
        for prefix, count in {"REF": 15, "PRES": 23, "TEX": 20, "ARCH": 27, "CI": 11, "OPS": 12}.items():
            for number in range(1, count + 1):
                identity = f"{prefix}-{number:02}"
                level = ("authorized_rollout" if prefix == "OPS" else "integration" if identity in {"ARCH-14", "ARCH-23"}
                    else "live_pr" if identity in {"CI-01", "CI-02", "CI-04", "CI-05", "CI-08", "CI-11"}
                    else "review" if identity == "CI-10" else "unit")
                cases.append({"id": identity, "level": level, "status": "DEFERRED_BY_USER" if prefix == "OPS" else "PASS", "checked_sha": synthetic})
        good = {"maintenance_context": {"repository": m.REPOSITORY, "pr_number": 77, "head_H": head, "base_B": base, "synthetic_S": synthetic},
            "registry_source": {"commit": tooling}, "cases": cases,
            "completion_policy": {"all108_complete": False, "overall_F3_closed": False},
            "scientific_exclusions": {"new_or_changed_theorem_declarations": 0, "new_mathematical_assumptions": 0, "scientific_promotion": False},
            "receipt_assembly": {"source_context": {"head_sha": head, "base_sha": base, "checked_sha": synthetic}},
            "additional_acceptance_conditions": [{"status": "PASS", "checked_sha": synthetic, "production_tooling_source": {"commit": tooling}}]}
        m.verify_ledger(good, head, base, synthetic, tooling, True)
        checks.append({"case": "synthetic_ledger_positive", "status": "PASS"})
        stale = deepcopy(good)
        stale["maintenance_context"]["head_H"] = "5" * 40
        rejected("stale_ledger_head", lambda: m.verify_ledger(stale, head, base, synthetic, tooling, True), "source H/B/S/T differs")
        stale = deepcopy(good)
        stale["cases"][0]["checked_sha"] = "5" * 40
        rejected("stale_unit_case", lambda: m.verify_ledger(stale, head, base, synthetic, tooling, True), "not bound to current S")
        stale = deepcopy(good)
        stale["cases"][-1]["status"] = "PASS"
        rejected("OPS_promotion", lambda: m.verify_ledger(stale, head, base, synthetic, tooling, True), "promoted case")
        # Real publisher layout with fixture content; repair ZIP digests before
        # semantic adversaries so a checksum failure cannot mask source checks.
        prefix = "hardening-pr77-finalized-acceptance/"
        reports, captures, publisher, actual_checks = {}, {}, {"artifacts": []}, []
        def repack(artifact, value, extra=False):
            stream = io.BytesIO()
            with zipfile.ZipFile(stream, "w") as archive:
                archive.writestr("required-source.json", m.json_bytes(value))
                if extra:
                    archive.writestr("unreviewed.json", b"{}")
            payload = stream.getvalue()
            captures[prefix + artifact + ".zip"] = payload
            record = next(row for row in publisher["artifacts"] if row["name"] == artifact)
            record.update(sha256=m.sha(payload), bytes=len(payload))
        tree = "6" * 40
        for number, (artifact, context) in enumerate(m.LEGACY_CONTEXT_ARTIFACTS.items(), 1):
            reports[artifact] = {"format": "Permansson.Hardening.CIContext.v1", "repository": m.REPOSITORY,
                "accepted_release": m.ACCEPTED, "checked_sha": synthetic, "checked_tree": tree,
                "event": "pull_request", "pr_number": 77, "head_sha": head, "base_sha": base,
                "scope": "canonical_commit_objects", "run_id": 1000 + number,
                "run_attempt": 1, "event_sha256": "7" * 64}
            publisher["artifacts"].append({"name": artifact})
            actual_checks.append({"name": context, "id": 2000 + number,
                "details_url": f"https://github.com/HMarcusWH/PermanssonLean/actions/runs/{1000+number}/job/{2000+number}"})
            repack(artifact, reports[artifact])
        def verify_contexts():
            m.verify_legacy_contexts(captures, prefix, actual_checks, publisher, head, base, synthetic, tree)
        verify_contexts()
        checks.append({"case": "five_current_legacy_context_ZIPs_positive", "status": "PASS"})
        artifact = next(iter(reports))
        original = deepcopy(reports[artifact])
        for field, value in (("head_sha", "8" * 40), ("event", "workflow_dispatch"), ("run_id", 9999)):
            altered = dict(original, **{field: value})
            repack(artifact, altered)
            rejected("legacy_context_repaired_" + field, verify_contexts, "actual current PR/check run")
        repack(artifact, original, extra=True)
        rejected("legacy_context_extra_ZIP_member", verify_contexts, "exactly required-source.json")
        repack(artifact, original)
        publisher["artifacts"][0]["sha256"] = "0" * 64
        rejected("legacy_context_publisher_digest", verify_contexts, "publisher/ZIP identity differs")
        repack(artifact, original)
        del captures[prefix + artifact + ".zip"]
        rejected("legacy_context_missing_ZIP", verify_contexts, "publisher/ZIP identity differs")
        # A separate main-push addendum uses inert fixture M and acquisition
        # envelopes, never manufactured actual postmerge acceptance evidence.
        main = "9" * 40
        postdir = "hardening-pr77-finalized-main-push"
        postprefix = postdir + "/"
        postset, postchecks, postruns, runs_by_context = {}, [], [], {}
        context_groups = [("build",), ("research",), ("executable-verification",),
            ("Application contract (ubuntu-latest)", "Application contract (windows-latest)"),
            ("frozen-source-preservation", "release-export-integrity", "archive-reproducibility"),
            ("integrity-portability-windows",)]
        for run_number, group in enumerate(context_groups, 10):
            postruns.append({"id": run_number, "head_sha": main, "event": "push", "head_branch": "main",
                "status": "completed", "conclusion": "success", "repository": {"full_name": m.REPOSITORY}})
            for context in group:
                job = 3000 + len(postchecks)
                postchecks.append({"id": job, "name": context, "head_sha": main, "status": "completed",
                    "conclusion": "success", "app": {"id": 15368},
                    "details_url": f"https://github.com/HMarcusWH/PermanssonLean/actions/runs/{run_number}/job/{job}"})
                runs_by_context[context] = run_number
        postsummary = {"status": "PASS", "source": {"main": main, "tree": tree, "head": head,
                                                   "base": base, "synthetic": synthetic}, "artifacts": []}
        def push_report(context):
            return {"format": "Permansson.Hardening.CIContext.v1", "repository": m.REPOSITORY,
                "accepted_release": m.ACCEPTED, "checked_sha": main, "checked_tree": tree,
                "event": "push", "pr_number": None, "head_sha": None, "base_sha": None,
                "scope": "canonical_commit_objects", "run_id": runs_by_context[context],
                "run_attempt": 1, "event_sha256": "7" * 64}
        def postzip(artifact, member, value):
            stream = io.BytesIO()
            with zipfile.ZipFile(stream, "w") as archive:
                archive.writestr(member, m.json_bytes(value))
            payload = stream.getvalue()
            postset[postprefix + artifact + ".zip"] = payload
            existing = next((row for row in postsummary["artifacts"] if row["name"] == artifact), None)
            if existing is None:
                existing = {"name": artifact}
                postsummary["artifacts"].append(existing)
            existing.update(sha256=m.sha(payload), bytes=len(payload))
        for artifact, context in m.LEGACY_CONTEXT_ARTIFACTS.items():
            postzip(artifact, "required-source.json", push_report(context))
        for artifact, context in (("hardening-preservation-reports", "frozen-source-preservation"),
            ("hardening-export-reports", "release-export-integrity"),
            ("hardening-archive-reports", "archive-reproducibility"),
            ("hardening-windows-portability-reports", "integrity-portability-windows")):
            postzip(artifact, "context.json", push_report(context))
        postzip("d0-finite-calculation-evidence", "fixture.json", {"fixture": True})
        postcommit = {"sha": main, "parents": [{"sha": base}, {"sha": head}], "tree": {"sha": tree}}
        research_job = next(row for row in postchecks if row["name"] == "research")
        postjobs = {"jobs": [{"id": research_job["id"], "conclusion": "success", "steps": [
            {"name": "Generate and independently verify C10 release proof evidence", "conclusion": "skipped"},
            {"name": "Upload source-bound C10 proof evidence", "conclusion": "skipped"}]}]}
        def verify_push():
            for name, value in (("main-checks.json", {"check_runs": postchecks}),
                                ("main-runs.json", {"workflow_runs": postruns}),
                                ("main-commit.json", postcommit), ("research-jobs.json", postjobs)):
                postset[postprefix + name] = m.json_bytes({"fetched_at": "FIXTURE", "response": value})
            postset[postprefix + "verification-summary.json"] = m.json_bytes(postsummary)
            m.verify_postmerge_capture(postset, postdir, head, base, synthetic, tree, main)
        verify_push()
        checks.append({"case": "separate_main_push_addendum_positive_9checks_6runs_10ZIPs", "status": "PASS"})
        postchecks[0]["head_sha"] = synthetic
        rejected("main_push_stale_check", verify_push, "nine actual successful current-main")
        postchecks[0]["head_sha"] = main
        postruns[0]["event"] = "workflow_dispatch"
        rejected("main_push_manual_run", verify_push, "six actual main-push workflows")
        postruns[0]["event"] = "push"
        postcommit["parents"].reverse()
        rejected("main_push_wrong_API_parents", verify_push, "API commit parent/tree")
        postcommit["parents"].reverse()
        artifact = next(iter(m.LEGACY_CONTEXT_ARTIFACTS))
        context = m.LEGACY_CONTEXT_ARTIFACTS[artifact]
        postzip(artifact, "required-source.json", dict(push_report(context), head_sha=head))
        rejected("main_push_repaired_legacy_PR_fields", verify_push, "actual current main-push/check run")
        postzip(artifact, "required-source.json", push_report(context))
        postzip("hardening-preservation-reports", "context.json",
                dict(push_report("frozen-source-preservation"), checked_sha=synthetic))
        rejected("main_push_repaired_integrity_stale_source", verify_push, "integrity context is not")
        postzip("hardening-preservation-reports", "context.json", push_report("frozen-source-preservation"))
        postjobs["jobs"][0]["steps"][0]["conclusion"] = "success"
        rejected("main_push_C10_not_skipped", verify_push, "C10 generation/upload was not reported skipped")
        postjobs["jobs"][0]["steps"][0]["conclusion"] = "skipped"
        postsummary["artifacts"].append({"name": "c10-release-evidence"})
        rejected("main_push_C10_extra_artifact", verify_push, "ten publisher ZIPs and no PR-only C10")
        postsummary["artifacts"].pop()
        postsummary["artifacts"][0]["sha256"] = "0" * 64
        rejected("main_push_publisher_digest", verify_push, "publisher/ZIP bytes differ")
        output = root / "maintenance-evidence/v020-hardening-77"
        args = Namespace(workspace=str(artifacts.parent), head=m.REJECTED_HEAD, base=base,
                         synthetic=synthetic, tooling=tooling, output=str(output))
        rejected("Habcc_never_final", lambda: m.assemble(args), "cannot be certified")
        if output.exists():
            raise ValueError("Rejected old-head build wrote output")
    return {"format": "Permansson.ReceiptBuilderSelfcheck.v1", "status": "PASS", "checks": checks,
        "count": len(checks), "helper_sha256": m.sha((artifacts / "build_maintenance_receipt_packet.py").read_bytes()),
        "control_script_sha256": m.sha(Path(__file__).read_bytes()),
        "scope": "Curated historical files and disposable fixtures only. No final receipt built, no Habcc acceptance promoted, no repository mutations."}


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--scratch", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    result = run(Path(__file__).resolve().parent, args.scratch)
    with args.report.open("xb") as stream:
        stream.write(m.json_bytes(result))
    print(json.dumps({"status": result["status"], "checks": result["count"], "helper_sha256": result["helper_sha256"]}))

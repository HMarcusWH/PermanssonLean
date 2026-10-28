"""Fast read-only PR113 engineering QA, never a substitute for required CI.

Run real Python syntax checks and selected mock-only adversarial unit suites,
without executing >1,500-test Research Lean discovery or changing any
historically pinned .github/workflows context. Full original Lean, archive
and scholarly gates remain mandatory.
"""
from __future__ import annotations
import argparse
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
TEST_ROOT = ROOT/"verification/research"
SOURCE_ROOTS = (TEST_ROOT, ROOT/"release/mathematical-closure-1")
SUITES = (
    # The versioned migration and actual detached 30-source CI-06/CI-07
    # executions must be present before the whole producer may pass.
    "test_pr113_tooling_migration_v2.py",
    "test_pr113_a2_successor_identity_v2.py",
    "test_pr113_a2_compiler_route_v3.py",
    "test_pr113_historical_a2_replay_v1.py",
    "test_pr113_historical_a2_baseline_v1.py",
    "test_pr113_a2_dependency_bridge_v2.py",
    "test_pr113_corrected_a2_intake.py",
    "test_pr113_disposable_transition_rehearsal.py",
    "test_pr113_v2_runtime.py",
    "test_pr113_t2_intake_v2.py",
    "test_pr113_archive_pre_activation_rehearsal_v1.py",
    "test_pr113_t2_execution_io_v1.py",
    # The actual pinned Lean A2 positive/negative compiler runs in its
    # separately configured historical-A2 producer job with lean-action.
    "test_pr113_a2_successor_identity.py",
    "test_pr113_dual_a2_compiler.py",
    "test_pr113_dual_tooling_candidate.py",
    "test_pr113_dual_review_packet.py",
    "test_pr113_required_dual_gate.py",
    "test_pr113_historical_postmerge.py",
    "test_pr113_historical_artifact_delivery.py",
    "test_pr113_inactive_required_gate_replacement.py",
    "test_pr113_full_required_workflow_preview.py",
    "test_pr113_atomic_migration_preview.py",
    # Real phase-aware A2 input contract and exact historical Git source pin.
    # These are Python-only source/receipt tests; genuine Lean and the old
    # isolated historical executor remain separate mandatory CI.
    "test_localized_prefix_integrity.py",
    "test_pr113_phase_aware_a2_consumer.py",
    "test_pr113_boundary_hardening_20261027.py",
    "test_pr113_semantic_receipt_v2.py",
    "test_pr113_historical_evidence_contract_v2.py",
    "test_pr113_inheritance_optimized.py",
    "test_pr113_v2_workflow_contract_preview.py",
    "test_pr113_draft_rehearsal_auth.py",
    "test_pr113_tooling_migration.py",
    "test_pr113_final_source_readiness.py",
    "test_final_closure_v3_source_readiness.py",
    "test_final_closure_positive_route_candidate.py",
    "test_final_closure_claim_controls_candidate.py",
    "test_final_closure_assemble_v3.py",
    "test_final_closure_batch_legacy_replay.py",
    "test_final_closure_producer_bytes.py",
    "test_final_closure_extra_producers_v31.py",
    "test_final_closure_reproduction_auth.py",
    "test_final_closure_postseal_auth.py",
    "test_final_postseal_replay.py",
    "test_final_closure_schema.py",
    "test_clean_source_reproduction.py",
    # Focused source guards must fail fast before 1,500+ research regressions.
    "test_final_closure_compiler_diagnostic_retention.py",
    "test_pr113_full_inventory_gate.py",
    "test_pr113_mandatory_v31.py",
    "test_pr113_v31_execution_integrity.py",
    "test_pr113_v31_seal_entry.py",
    "test_pr113_preseal_input_carrier.py",
    "test_pr113_original_producer_trigger_candidate.py",
    "test_pr113_original21_live_catalog.py",
    "test_pr113_legacy20_runtime_resolution.py",
    "test_pr113_workflow_proposal_boundary.py",
    "test_pr113_release_target.py",
    "test_pr113_infrastructure_acceptance.py",
    "test_pr113_legacy20_choice_delivery.py",
    "test_pr113_implementation_matrix.py",
    "test_pr113_successor_workflow_profile.py",
)
FORMAT = "Permansson.PR113.FastEngineeringPreflight.v1"


class PreflightError(ValueError):
    pass


def require(ok, msg):
    if not ok:
        raise PreflightError(msg)


def run_cli(args, timeout):
    try:
        return subprocess.run(args,cwd=ROOT,capture_output=True,
                              text=True,timeout=timeout)
    except (OSError,subprocess.TimeoutExpired) as exc:
        raise PreflightError("fast-source tool failed or timed out") from exc


def inspect_source_tree():
    rows=[]
    for src in SOURCE_ROOTS:
        require(src.is_dir() and not src.is_symlink(),
                "expected original Python source root is unavailable")
        for p in sorted(src.rglob("*.py")):
            require(p.is_file() and not p.is_symlink(),
                    "Python source symlink or missing source")
            raw=p.read_bytes()
            require(len(raw)<=4*1024*1024,
                    "unexpectedly oversized Python source")
            try:
                ast.parse(raw.decode("utf-8"),filename=str(p))
            except (SyntaxError,UnicodeError) as exc:
                raise PreflightError(
                    "unparseable original Python module: "+
                    p.relative_to(ROOT).as_posix()) from exc
            rows.append((p.relative_to(ROOT).as_posix(),
                         hashlib.sha256(raw).hexdigest()))
    return rows


def execute(head, output):
    require(isinstance(head,str) and re.fullmatch("[0-9a-f]{40}",head),
            "actual source H required")
    branch=run_cli(["git","rev-parse","HEAD"],30)
    require(branch.returncode==0 and branch.stdout.strip()==head,
            "preflight source checkout differs from requested exact H")
    base=run_cli(["git","status","--porcelain=v1","--untracked-files=all",
                  "--","verification/research",
                  "release/mathematical-closure-1"],30)
    require(base.returncode==0 and not base.stdout.strip(),
            "original engineering test/tooling source is dirty or untracked")
    output=Path(output)
    require(not output.is_symlink(),"fast report output symlink prohibited")
    output=output.resolve()
    require(not output.exists() and
            not output.is_relative_to(ROOT.resolve()) and
            not ROOT.resolve().is_relative_to(output),
            "fast output must be a new independent external directory")
    output.mkdir(parents=True)
    modules=inspect_source_tree()
    tests=[]
    total_ok=True
    for pattern in SUITES:
        require((TEST_ROOT/pattern).is_file(),
                "expected source-controlled QA suite missing")
        result=run_cli(
            [sys.executable,"-B","-m","unittest","discover",
             "-s",str(TEST_ROOT),"-p",pattern,"-v"],120)
        name=pattern.removesuffix(".py")
        combined=(result.stdout+"\n"+result.stderr)
        (output/(name+".log")).write_text(combined)
        ok=result.returncode==0 and "Ran " in combined and "OK" in combined and \
           "FAILED (" not in combined and "skipped=" not in combined
        total_ok=total_ok and ok
        tests.append({
            "module":pattern,
            "passed":ok,
            "returncode":result.returncode,
            "log_sha256":hashlib.sha256(combined.encode()).hexdigest(),
        })
    changed=run_cli(
        ["git","status","--porcelain=v1","--untracked-files=all",
         "--","verification/research","release/mathematical-closure-1"],30)
    require(changed.returncode==0 and not changed.stdout.strip(),
            "test execution modified tracked/untracked source")
    report={
        "format":FORMAT,
        "status":"FAST_ENGINEERING_QA_PASS" if total_ok else "FAST_ENGINEERING_QA_FAIL",
        "source_head":head,
        "python_modules_ast_parsed":len(modules),
        "source_blob_digest":hashlib.sha256(json.dumps(
            modules,separators=(",",":"),sort_keys=True).encode()).hexdigest(),
        "test_modules_executed":len(tests),
        "test_results":tests,
        "original_A2_security_gate_passed":False,
        "historical_T_archive_gate_passed":False,
        "independent_security_review":False,
        "independent_mathematical_review":False,
        "scholarly_release_approved":False,
    }
    (output/"fast_preflight.json").write_text(
        json.dumps(report,sort_keys=True,indent=2)+"\n")
    require(total_ok,"one or more nonhistorical source regression tests failed")
    return report


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--head",required=True)
    p.add_argument("--out",required=True,type=Path)
    a=p.parse_args(argv)
    try:
        report=execute(a.head,a.out)
    except (PreflightError,OSError,ValueError) as exc:
        print("PR113 FAST QA FAILED:",exc,file=sys.stderr)
        return 2
    print(json.dumps({"status":report["status"],
                      "source_head":report["source_head"],
                      "tests":report["test_modules_executed"]},sort_keys=True))
    return 0

if __name__=="__main__":
    raise SystemExit(main())

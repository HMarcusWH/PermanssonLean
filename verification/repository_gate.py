#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import py_compile
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEX = ROOT / "paper" / "Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_2026-09-23.tex"
RELEASE_META = ROOT / "docs" / "releases" / "v0.1.8.json"
MANIFEST = ROOT / "docs" / "PAPER_VERIFICATION_MANIFEST.md"
README = ROOT / "README.md"
FORMAL_MAP = ROOT / "docs" / "FORMALIZATION_MAP.md"
VERIFY_README = ROOT / "verification" / "README.md"
SUITE_README = ROOT / "verification" / "destructive" / "suite" / "README_RERUN.md"
SUITE_SUMMARY = ROOT / "verification" / "destructive" / "suite" / "FULL_SUITE_SUMMARY.json"
LEGACY_SUMMARY = ROOT / "verification" / "destructive" / "suite" / "results" / "v016_legacy_pass_ledger_compact.json"
HISTORICAL_GATES_README = ROOT / "verification" / "v0.1.8_release_gate" / "prior_gates_31_33" / "README.md"
LEAN_CROSSWALK = ROOT / "verification" / "lean" / "LEAN_DECLARATION_CROSSWALK.json"
ROOT_IMPORT_SNAPSHOT = ROOT / "verification" / "lean" / "PermanssonLean_root_imports_snapshot.lean"
ROOT_IMPORT_ACTUAL = ROOT / "PermanssonLean.lean"
CITATION = ROOT / "CITATION.cff"
LEAN_TOOLCHAIN = ROOT / "lean-toolchain"
LAKEFILE = ROOT / "lakefile.toml"
PY_REQUIREMENTS = ROOT / "verification" / "destructive" / "suite" / "requirements.txt"

EXPECTED_TEX = "8235f6140bca33e7e3f0e96b4fd3aa2431c476fbdaf7c5d86d6d0b703ea54ed9"
EXPECTED_PDF = "24f7dd43c8996b6fc8bedf708704969ba2124e159783bbd2ded45db61525df54"
EXPECTED_FROZEN = "7ab578c928a2918e09846b9f1c425f5a6c07b5b5dd0a0c8728662eebcb69a15a"
EXPECTED_PORTABLE = "864e2fec88b345194b0a9dc4ce9431e6a9a754eb88adea75fb8835b6244f41c3"
EXPECTED_RELEASE = "66a13d3d4ea6854d38a6a32fe8b7946cbc290c62484b654dc02e0317039faf25"
LEAN_SNAPSHOT = "c018f79ea4ce46f4f679ad5bca254509778fc53c"
LEAN_CI = "35808810682"

checks: list[tuple[str, bool, str]] = []

def add(name: str, ok: bool, detail: str = "") -> None:
    checks.append((name, bool(ok), detail))

def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()

add("paper_tex_present", TEX.is_file(), str(TEX))
add("paper_tex_sha256", TEX.is_file() and sha256(TEX) == EXPECTED_TEX,
    sha256(TEX) if TEX.is_file() else "missing")

tex = TEX.read_text(encoding="utf-8", errors="replace") if TEX.is_file() else ""
add("appendix_d_present", "Appendix D - Formal Verification and Reproducibility" in tex)
add("appendix_e_present", "Appendix E - Specialized Finite-Certificate and Rigidity Extensions" in tex)
add("formal_snapshot_cited", LEAN_SNAPSHOT in tex)
add("formal_ci_cited", LEAN_CI in tex)
add("old_section_11_5_heading_absent", "11.5 Finite-certificate and rigidity programme" not in tex)

for run, path in [
    (17, ROOT / "verification/destructive/suite/scripts/run17_killed_kernel_persistence.py"),
    (18, ROOT / "verification/destructive/suite/scripts/run18_qsd_pathologies.py"),
    (19, ROOT / "verification/destructive/suite/scripts/run19_polish_descriptor_space.py"),
    (20, ROOT / "verification/destructive/suite/scripts/run20_finite_horizon_perturbation.py"),
    (21, ROOT / "verification/destructive/suite/scripts/run21_infinite_horizon_failure_modes.py"),
    (22, ROOT / "verification/destructive/suite/scripts/run22_margin_preservation.py"),
    (23, ROOT / "verification/destructive/suite/scripts/run23_intervention_family_signatures.py"),
    (24, ROOT / "verification/destructive/suite/scripts/run24_intervention_quotient.py"),
    (25, ROOT / "verification/destructive/suite/scripts/run25_scalar_defect.py"),
    (26, ROOT / "verification/destructive/suite/scripts/run26_finite_detection.py"),
    (27, ROOT / "verification/destructive/suite/scripts/run27_first_bad_schur.py"),
    (28, ROOT / "verification/destructive/suite/scripts/run28_singular_compatibility.py"),
    (29, ROOT / "verification/destructive/suite/scripts/run29_specialized_novel_math.py"),
    (30, ROOT / "verification/destructive/suite/scripts/run30_integrated_gate.py"),
]:
    add(f"run_{run}_source_present", path.is_file(), str(path))

for run, path in [
    (31, ROOT / "verification/v0.1.8_release_gate/prior_gates_31_33/run31_release_gate.py"),
    (32, ROOT / "verification/v0.1.8_release_gate/prior_gates_31_33/run32_figure_correction_gate.py"),
    (33, ROOT / "verification/v0.1.8_release_gate/prior_gates_31_33/run33_final_figure3_layout_gate.py"),
    (34, ROOT / "verification/v0.1.8_release_gate/run34_editorial_final_release_gate.py"),
]:
    add(f"run_{run}_gate_source_present", path.is_file(), str(path))

if RELEASE_META.is_file():
    meta = json.loads(RELEASE_META.read_text(encoding="utf-8"))
    paper = meta.get("paper", {})
    add("release_meta_pdf_hash", paper.get("pdf_sha256") == EXPECTED_PDF, str(paper.get("pdf_sha256")))
    add("release_meta_tex_hash", paper.get("tex_sha256") == EXPECTED_TEX, str(paper.get("tex_sha256")))
    destructive = meta.get("destructive_verification", {})
    add("release_meta_frozen_hash", destructive.get("archive_sha256") == EXPECTED_FROZEN, str(destructive.get("archive_sha256")))
    add("release_meta_portable_hash", destructive.get("windows_safe_archive_sha256") == EXPECTED_PORTABLE, str(destructive.get("windows_safe_archive_sha256")))
    gate = meta.get("release_gate", {})
    add("release_meta_run34", gate.get("run") == 34 and gate.get("passed") == 58 and gate.get("total") == 58,
        json.dumps(gate, sort_keys=True))
    distribution = meta.get("distribution_packaging", {})
    add("release_meta_outer_zip_hash", distribution.get("windows_safe_release_sha256") == EXPECTED_RELEASE,
        str(distribution.get("windows_safe_release_sha256")))
    repo_ver = meta.get("repository_verification", {})
    add("release_meta_python_pin", repo_ver.get("python") == "3.13" and repo_ver.get("numpy") == "2.5.3",
        json.dumps(repo_ver, sort_keys=True))
else:
    add("release_metadata_present", False, str(RELEASE_META))

manifest = MANIFEST.read_text(encoding="utf-8") if MANIFEST.is_file() else ""
for name, needle in [
    ("manifest_pdf_hash", EXPECTED_PDF),
    ("manifest_tex_hash", EXPECTED_TEX),
    ("manifest_frozen_hash", EXPECTED_FROZEN),
    ("manifest_portable_hash", EXPECTED_PORTABLE),
    ("manifest_release_hash", EXPECTED_RELEASE),
    ("manifest_run34", "58/58"),
    ("manifest_lean_snapshot", LEAN_SNAPSHOT),
    ("manifest_python_pin", "CPython 3.13"),
    ("manifest_numpy_pin", "NumPy 2.5.3"),
]:
    add(name, needle in manifest, needle)


readme = README.read_text(encoding="utf-8") if README.is_file() else ""
formal_map = FORMAL_MAP.read_text(encoding="utf-8") if FORMAL_MAP.is_file() else ""
verify_readme = VERIFY_README.read_text(encoding="utf-8") if VERIFY_README.is_file() else ""
suite_readme = SUITE_README.read_text(encoding="utf-8") if SUITE_README.is_file() else ""
citation = CITATION.read_text(encoding="utf-8") if CITATION.is_file() else ""
add("readme_exact_paper_title",
    "Permansson Regimes: A General Framework for Strategic Dynamics Beyond Equilibrium v0.1.8" in readme)
add("formal_map_no_stale_promotion_language",
    "promoted theorem obligation" not in formal_map and "promoted formal claim" not in formal_map and "non-promoted" not in formal_map)
add("formal_map_appendix_e_boundary", "Appendix E specialized finite-certificate / rigidity extensions" in formal_map)
add("verification_readme_no_missing_baseline_dir", "`baseline/`" not in verify_readme)
add("verification_readme_package_gate_boundary",
    "package-level" in verify_readme and "does not duplicate those binary release artifacts" in verify_readme)
add("suite_readme_source_contract_boundary",
    "V017_SOURCE_CONTRACT.txt" in suite_readme and "authoritative evidentiary record" in suite_readme)
add("historical_gate_readme_present", HISTORICAL_GATES_README.is_file(), str(HISTORICAL_GATES_README))

if SUITE_SUMMARY.is_file():
    ss = json.loads(SUITE_SUMMARY.read_text(encoding="utf-8"))
    r = ss.get("runs_17_30", {})
    add("suite_summary_3240", r.get("checks_passed") == 3240 and r.get("checks_total") == 3240 and r.get("checks_failed") == 0,
        json.dumps(r, sort_keys=True))
else:
    add("suite_summary_3240", False, "missing")

if LEGACY_SUMMARY.is_file():
    ls = json.loads(LEGACY_SUMMARY.read_text(encoding="utf-8"))
    add("legacy_summary_explicitly_compact",
        ls.get("status") == "PASS" and ls.get("passed") == 85 and ls.get("total") == 85
        and "compact" in str(ls.get("evidence_type", "")).lower()
        and "not a reconstruction" in str(ls.get("note", "")).lower(),
        json.dumps(ls, sort_keys=True))
else:
    add("legacy_summary_explicitly_compact", False, "missing")

if LEAN_CROSSWALK.is_file():
    cw = json.loads(LEAN_CROSSWALK.read_text(encoding="utf-8"))
    add("lean_crosswalk_17_entries",
        cw.get("commit") == LEAN_SNAPSHOT and cw.get("all_found") is True
        and len(cw.get("declarations", [])) == 17
        and cw.get("selection_count") == 17
        and "selected" in str(cw.get("scope", "")).lower()
        and all(x.get("found_at_commit") for x in cw.get("declarations", [])),
        str(len(cw.get("declarations", []))))
else:
    add("lean_crosswalk_17_entries", False, "missing")

if ROOT_IMPORT_ACTUAL.is_file() and ROOT_IMPORT_SNAPSHOT.is_file():
    actual_imports = [x.strip() for x in ROOT_IMPORT_ACTUAL.read_text(encoding="utf-8").splitlines() if x.strip().startswith("import ")]
    snapshot_imports = [x.strip() for x in ROOT_IMPORT_SNAPSHOT.read_text(encoding="utf-8").splitlines() if x.strip().startswith("import ")]
    add("root_import_snapshot_exact", actual_imports == snapshot_imports, f"{len(actual_imports)} vs {len(snapshot_imports)}")
else:
    add("root_import_snapshot_exact", False, "missing actual or snapshot")

add("citation_v018", 'version: "0.1.8"' in citation and "A General Framework for Strategic Dynamics Beyond Equilibrium" in citation)
add("lean_toolchain_4_34", LEAN_TOOLCHAIN.is_file() and LEAN_TOOLCHAIN.read_text(encoding="utf-8").strip() == "leanprover/lean4:v4.34.0")
lake = LAKEFILE.read_text(encoding="utf-8") if LAKEFILE.is_file() else ""
add("mathlib_4_34_pinned", 'rev = "v4.34.0"' in lake)
requirements = PY_REQUIREMENTS.read_text(encoding="utf-8").strip() if PY_REQUIREMENTS.is_file() else ""
add("numpy_2_5_3_pinned", requirements == "numpy==2.5.3", requirements)

python_files = sorted((ROOT / "verification").rglob("*.py"))
syntax_failures: list[str] = []
for path in python_files:
    try:
        py_compile.compile(str(path), doraise=True)
    except Exception as exc:
        syntax_failures.append(f"{path.relative_to(ROOT)}: {exc}")
add("python_sources_compile", not syntax_failures, "; ".join(syntax_failures))
add("python_source_count", len(python_files) >= 20, str(len(python_files)))

failed = [(n, d) for n, ok, d in checks if not ok]
for name, ok, detail in checks:
    print(f"{'PASS' if ok else 'FAIL'} {name}" + (f" — {detail}" if detail else ""))
print(f"\nTOTAL {len(checks) - len(failed)}/{len(checks)}")
if failed:
    sys.exit(1)

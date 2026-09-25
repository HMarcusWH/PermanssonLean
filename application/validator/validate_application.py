#!/usr/bin/env python3
"""Validate a declared application contract, never the truth of its claims.

All schemas are local. Artifacts are read-only, bundle-local, and hash checked.
See APPLICATION_STANDARD.md for the deliberately limited scope of this validator.
"""
from __future__ import annotations

import argparse
from collections import deque
from datetime import datetime
from decimal import Decimal
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import re
import sys
from typing import Any

from jsonschema import Draft202012Validator, FormatChecker
from referencing import Registry, Resource
from referencing.exceptions import NoSuchResource

APP = Path(__file__).resolve().parents[1]
SCHEMA_BASE = "https://hmwh.se/schemas/permansson/application/0.1.0/"
MAX_JSON_BYTES = 2 * 1024 * 1024
MAX_ARTIFACT_BYTES = 8 * 1024 * 1024
ROOT_KINDS = {"EXTERNAL_EVIDENCE", "DECLARED_IDENTITY_OR_AXIOM", "INDEPENDENT_UPSTREAM_RESULT"}
STRATEGIC = {"ACTION_SELECTION", "STRATEGIC_UPDATE", "STRATEGIC_GENERATOR"}
ASSESSMENTS = {"formal_admissibility", "reachable_support", "causal_modularity"}
NOTICE = "Contract validation only: no scientific truth, proof, causal identification, coverage, or authentic freeze is verified."


def _pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def _bad_constant(value: str) -> None:
    raise ValueError(f"Non-finite JSON number: {value}")


def _float(value: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed):
        raise ValueError("Non-finite JSON number")
    return parsed


def load_json(path: Path) -> Any:
    with path.open("rb") as stream:
        raw = stream.read(MAX_JSON_BYTES + 1)
    if len(raw) > MAX_JSON_BYTES:
        raise ValueError("JSON document exceeds 2 MiB")
    return json.loads(raw.decode("utf-8"), object_pairs_hook=_pairs,
                      parse_constant=_bad_constant, parse_float=_float)


def _timestamp(value: str) -> tuple[datetime, Decimal]:
    """Return an exactly ordered instant without truncating fractional seconds.

    datetime handles the calendar and numeric offset at whole-second precision.
    Decimal is constructed directly from the fractional digits, without arithmetic
    or context rounding. Tuple comparison therefore preserves every supplied digit.
    """
    match = re.fullmatch(
        r"(?P<whole>[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2})"
        r"(?:\.(?P<fraction>[0-9]+))?(?P<offset>Z|[+-][0-9]{2}:[0-9]{2})",
        value,
    )
    if match is None:
        raise ValueError("A timezone-qualified RFC3339 timestamp is required")
    offset = match["offset"]
    if offset != "Z":
        if int(offset[1:3]) > 23 or int(offset[4:6]) > 59 or offset == "-00:00":
            raise ValueError("Invalid or unknown timezone offset")
    parsed = datetime.fromisoformat(match["whole"] + offset.replace("Z", "+00:00"))
    if parsed.utcoffset() is None:
        raise ValueError("Timezone required")
    return parsed, Decimal("0." + (match["fraction"] or "0"))


FORMATS = FormatChecker()


@FORMATS.checks("date-time", raises=(ValueError, TypeError))
def _valid_timestamp(value: Any) -> bool:
    if not isinstance(value, str):
        return True  # Type errors belong to JSON Schema's type keyword.
    _timestamp(value)
    return True


def _deny_retrieval(uri: str) -> Resource:
    raise NoSuchResource(ref=uri)


@lru_cache(maxsize=1)
def validator() -> Draft202012Validator:
    resources = {}
    for path in sorted((APP / "schemas").glob("*.schema.json")):
        schema = load_json(path)
        Draft202012Validator.check_schema(schema)
        if schema["$id"] in resources:
            raise ValueError("Duplicate schema identifier")
        resources[schema["$id"]] = Resource.from_contents(schema)
    registry = Registry(retrieve=_deny_retrieval).with_resources(resources.items())
    return Draft202012Validator(
        resources[SCHEMA_BASE + "application_bundle.schema.json"].contents,
        registry=registry, format_checker=FORMATS,
    )


def _artifact_refs(value: Any) -> set[str]:
    refs: set[str] = set()
    if isinstance(value, dict):
        for key, item in value.items():
            if key == "bindings":
                refs.update(x for x in item.values() if x is not None)
            elif key.endswith("_ref") and isinstance(item, str):
                refs.add(item)
            else:
                refs.update(_artifact_refs(item))
    elif isinstance(value, list):
        for item in value:
            refs.update(_artifact_refs(item))
    return refs


def pipeline_digest(document: dict[str, Any]) -> str:
    """PERMANSSON_PIPELINE_V1 digest of declared semantics and referenced bytes.

    This is not RFC8785 and not an authentic timestamp. Registration receipts and
    post-evaluation assessments are intentionally outside the semantic digest.
    """
    pipeline = {k: v for k, v in document["semantic_pipeline"].items()
                if k not in {"pipeline_id", "registration_ref"}}
    protocols = [{k: v for k, v in j.items() if k not in ASSESSMENTS}
                 for j in document["interventions"]]
    refs = _artifact_refs([pipeline, protocols])
    artifacts = {a["id"]: a["sha256"] for a in document["artifacts"]}
    payload = {
        "domain": "PERMANSSON_PIPELINE_V1",
        "standard_version": document["standard_version"],
        "compatible_theory": document["compatible_theory"],
        "pipeline": pipeline, "interventions": protocols,
        "artifact_sha256": {key: artifacts[key] for key in sorted(refs)},
    }
    raw = json.dumps(payload, sort_keys=True, ensure_ascii=True,
                     separators=(",", ":"), allow_nan=False).encode("utf-8")
    return "sha256:" + hashlib.sha256(raw).hexdigest()


def safe_artifact(root: Path, relative: str) -> Path:
    """Reject traversal, ambiguous cross-platform paths, symlinks and non-files."""
    parts = relative.split("/")
    if (PurePosixPath(relative).is_absolute() or any(x in {"", ".", ".."} for x in parts)
            or any(not re.fullmatch(r"[A-Za-z0-9_.-]+", x) for x in parts)):
        raise ValueError("Artifact path must be a safe bundle-relative POSIX path")
    current = root.resolve()
    for part in parts:
        stem = part.split(".", 1)[0].upper()
        if (part.endswith(".") or stem in {"CON", "PRN", "AUX", "NUL"}
                or re.fullmatch(r"(?:COM|LPT)[1-9]", stem)):
            raise ValueError("Artifact path is not Windows-safe")
        current = current / part
        if current.is_symlink():
            raise ValueError("Artifact symlinks are forbidden")
    if not current.resolve().is_relative_to(root.resolve()) or not current.is_file():
        raise ValueError("Artifact is missing, not regular, or outside the bundle")
    return current


def artifact_digest(path: Path) -> str:
    with path.open("rb") as stream:
        raw = stream.read(MAX_ARTIFACT_BYTES + 1)
    if len(raw) > MAX_ARTIFACT_BYTES:
        raise ValueError("Artifact exceeds 8 MiB; use a bounded evidence snapshot")
    return hashlib.sha256(raw).hexdigest()


def validate_document(document: Any, root: Path) -> dict[str, Any]:
    errors: list[dict[str, str]] = []

    def fail(code: str, message: str) -> None:
        errors.append({"code": code, "message": message})

    def report() -> dict[str, Any]:
        return {"contract_valid": not errors, "scientific_claims_verified": False,
                "errors": errors, "notice": NOTICE}

    try:
        json.dumps(document, allow_nan=False)
    except (ValueError, TypeError, RecursionError) as exc:
        fail("JSON_VALUE", str(exc))
        return report()
    for error in validator().iter_errors(document):
        fail("SCHEMA", f"/{'/'.join(map(str, error.absolute_path))}: {error.message}")
    if errors:
        return report()

    def index(rows: list[dict[str, Any]], name: str) -> dict[str, dict[str, Any]]:
        found = {}
        for row in rows:
            if row["id"] in found:
                fail("DUPLICATE_ID", f"Duplicate {name} ID: {row['id']}")
            found[row["id"]] = row
        return found

    artifacts = index(document["artifacts"], "artifact")
    p, c, r, m = (document[key] for key in
                  ("semantic_pipeline", "certificate", "regime", "identified_set"))
    components = index(p["components"], "component")
    protocols = index(document["interventions"], "intervention")
    nodes = index(document["provenance_graph"]["nodes"], "provenance")
    used_paths: set[str] = set()
    for a in artifacts.values():
        if a["path"].casefold() in used_paths:
            fail("DUPLICATE_PATH", f"Duplicate/case-colliding artifact path: {a['path']}")
        used_paths.add(a["path"].casefold())
        try:
            path = safe_artifact(root, a["path"])
            if artifact_digest(path) != a["sha256"]:
                fail("ARTIFACT_HASH", f"Artifact changed: {a['id']}")
        except (OSError, ValueError) as exc:
            fail("ARTIFACT_PATH", f"{a['id']}: {exc}")
    missing = _artifact_refs(document) - artifacts.keys()
    for key in sorted(missing):
        fail("MISSING_ARTIFACT_REF", key)
    if not missing:
        expected = pipeline_digest(document)
        if p["pipeline_id"] != expected:
            fail("PIPELINE_DIGEST", f"Expected {expected}")
    if c["pipeline_id"] != p["pipeline_id"]:
        fail("CERTIFICATE_PIPELINE", "Certificate and semantic pipeline IDs differ")

    # Edges point from a claim/derivation to its dependencies. Audit every node,
    # including disconnected cycles, rather than only certificate-reachable nodes.
    remaining = {key: len(n["depends_on"]) for key, n in nodes.items()}
    parents: dict[str, list[str]] = {key: [] for key in nodes}
    for key, node in nodes.items():
        deps = node["depends_on"]
        if node["kind"] in ROOT_KINDS and deps:
            fail("ROOT_DEPENDENCIES", f"Declared evidence root has dependencies: {key}")
        if node["kind"] not in ROOT_KINDS and not deps:
            fail("ORPHAN_CLAIM", f"Non-root lacks supporting dependencies: {key}")
        for dep in deps:
            if dep not in nodes:
                fail("MISSING_NODE_REF", f"{key} -> {dep}")
            else:
                parents[dep].append(key)
    queue = deque(key for key, count in remaining.items() if count == 0)
    visited: set[str] = set()
    while queue:
        key = queue.popleft()
        visited.add(key)
        for parent in parents[key]:
            remaining[parent] -= 1
            if remaining[parent] == 0:
                queue.append(parent)
    if len(visited) != len(nodes) and all(d in nodes for n in nodes.values() for d in n["depends_on"]):
        fail("PROVENANCE_CYCLE", "Provenance contains a directed cycle")
    for owner in (c, r, m, m["uniform_gap"]):
        for key in owner["claim_refs"]:
            if key not in nodes or nodes[key]["kind"] != "CLAIM":
                fail("CLAIM_REF", f"Expected an existing CLAIM node: {key}")

    b = p["bindings"]
    if not {"ACTION_SELECTION", "STRATEGIC_UPDATE", "WORLD_TRANSITION", "FEASIBILITY"} <= {x["kind"] for x in components.values()}:
        fail("CANONICAL_COMPONENTS", "Inventory must explicitly retain alpha, U, P and feasibility")
    qsd_id = r["qsd_claim_id"]
    if qsd_id is not None and (qsd_id not in nodes or nodes[qsd_id]["kind"] != "CLAIM"):
        fail("QSD_CLAIM_REF", "QSD certificate must reference a CLAIM")
    if r["class"] == "QSD_CERTIFIED_QUASI_REGIME" and (qsd_id is None or qsd_id in r["claim_refs"]):
        fail("QSD_SEPARATE_GATES", "Link the QSD eigenmeasure and finite-persistence claims separately")
    for j in protocols.values():
        target, effective, fixed = (set(j[key]) for key in
                                    ("target_components", "effective_target_components", "held_fixed_components"))
        if not target <= effective or effective & fixed or effective | fixed != components.keys():
            fail("TARGET_PARTITION", f"{j['id']}: target closure and held-fixed inventory do not partition primitives")
        if (target | effective | fixed) - components.keys():
            fail("COMPONENT_REF", f"{j['id']}: unknown component")
        kinds = {components[key]["kind"] for key in effective if key in components}
        allowed = {
            "ACTION_SELECTION": {"ACTION_SELECTION"},
            "STRATEGIC_UPDATE": {"STRATEGIC_UPDATE"},
            "STRATEGIC_GENERATOR": {"ACTION_SELECTION", "STRATEGIC_UPDATE"},
            "WORLD_TRANSITION": {"WORLD_TRANSITION"},
        }
        if j["type"] in allowed and not kinds <= allowed[j["type"]]:
            fail("INTERVENTION_TYPE", f"{j['id']}: effective target contradicts intervention type")
        if j["schedule"] == "CLOCK_AUGMENTED" and b["clock_state"] is None:
            fail("CLOCK_REQUIRED", j["id"])
        if j["target_form"] == "ATOMIC" and len(target) != 1:
            fail("ATOMIC_TARGET", j["id"])
    if protocols and any(b[key] is None for key in ("property_map", "comparison_set")):
        fail("PROTOCOL_BINDING", "Interventions require a property map and comparison set")
    selected = protocols.get(c["intervention_id"])
    if c["intervention_id"] is not None and selected is None:
        fail("INTERVENTION_REF", "Certificate references an unknown intervention")
    if c["selection_status"] != p["selection_status"]:
        fail("SELECTION_STATUS", "Certificate and pipeline selection status differ")
    if p["selection_status"] == "FROZEN_REGISTERED":
        if p["frozen_at"] is None or _timestamp(p["frozen_at"]) > _timestamp(p["evaluation_started_at"]):
            fail("FREEZE_CHRONOLOGY", "Declared freeze must precede or equal evaluation start")
    if p["selection_status"] == "HELD_OUT_OR_SELECTION_ADJUSTED" and p["selection_adjustment_ref"] is None:
        fail("SELECTION_EVIDENCE", "Held-out/adjusted selection requires its procedure artifact")

    if r["class"] == "EXACT_GR":
        if r["exactness_basis"] == "NOT_ESTABLISHED" or not r["claim_refs"] or any(
                b[key] is None for key in ("limiting_law", "convergence_mode")):
            fail("EXACT_GR_EVIDENCE", "Exact GR requires a stated exact argument and occupation semantics")
    if r["class"] in {"QUASI_REGIME", "QSD_CERTIFIED_QUASI_REGIME"}:
        if r["horizon"] is None or r["eta"] is None or not r["claim_refs"]:
            fail("FINITE_PERSISTENCE", "A quasi-regime requires a horizon, eta and finite-persistence claim")
    if r["grounded"] and b["relevance_map"] is None:
        fail("RELEVANCE_REQUIRED", "Grounded claims require the frozen relevance map")

    if m["rule_ref"] != b["model_set_rule"] or m["inference_procedure_ref"] != b["inference_procedure"] or m["comparison_set_ref"] != b["comparison_set"]:
        fail("IDENTIFIED_SET_BINDING", "Model set/inference/comparison must use the frozen bindings")
    if c["identification_status"] != m["kind"] or c["direction_status"] != m["direction"] or c["uniform_gap_status"] != m["uniform_gap"]["status"]:
        fail("CERTIFICATE_DIMENSIONS", "Certificate dimensions disagree with the declared outer set")
    gap = m["uniform_gap"]
    if gap["status"] == "ESTABLISHED":
        if gap["lower_bound"] is None or Fraction(gap["lower_bound"]) <= 0 or not gap["claim_refs"] or m["quantification"] != "ALL_MODELS_ALL_COMPARISON_STATES" or m["zero_effect"] != "EXCLUDED":
            fail("UNIFORM_GAP", "An established gap needs a common positive bound over the full joint set")
    elif gap["lower_bound"] is not None:
        fail("UNIFORM_GAP", "Do not attach an established lower bound to an unresolved/NA gap")
    if not m["sampling_applicable"]:
        if m["coverage"] != "NOT_APPLICABLE" or c["statistical_status"] != "NOT_APPLICABLE":
            fail("STATISTICAL_STATUS", "No sampling: coverage/statistical status must be NOT_APPLICABLE")
    else:
        if m["coverage"] == "NOT_APPLICABLE" or c["statistical_status"] == "NOT_APPLICABLE":
            fail("STATISTICAL_STATUS", "Sampling uncertainty must be reported")
        if (m["coverage"] != "JUSTIFIED" or m["zero_effect"] in {"POSSIBLE", "NOT_ASSESSED"}) and c["statistical_status"] != "STATISTICALLY_UNRESOLVED":
            fail("STATISTICAL_RESOLUTION", "Uncovered or zero-containing outer set cannot resolve PR statistically")

    substantive = c["substantive_pr_status"]
    robust = substantive in {"ROBUST_PR", "ROBUST_NONCONSTITUTIVE_UNDER_FROZEN_PROTOCOL"}
    if substantive != "NOT_EVALUATED" and selected is None:
        fail("PROTOCOL_SCOPE", "Evaluated PR status requires one frozen protocol")
    if robust:
        required_zero = "EXCLUDED" if substantive == "ROBUST_PR" else "ALL_ZERO"
        if m["nonempty"] is not True or m["zero_effect"] != required_zero or m["kind"] == "STRUCTURALLY_UNRESOLVED" or m["quantification"] != "ALL_MODELS_ALL_COMPARISON_STATES" or not m["claim_refs"] or not c["claim_refs"]:
            fail("ROBUST_OUTER_SET", "Robust status requires the full joint model/state set and supporting claims")
        if selected is None or selected["type"] not in STRATEGIC or selected["formal_admissibility"] != "ADMISSIBLE":
            fail("STRATEGIC_PROTOCOL", "PR classification requires an admissible strategic intervention")
        if m["sampling_applicable"] and c["statistical_status"] != "RESOLVED_AT_DECLARED_COVERAGE":
            fail("ROBUST_STATISTICS", "Robust empirical classification requires resolved joint coverage")
    if substantive == "ROBUST_PR" and r["class"] != "EXACT_GR":
        fail("PR_REQUIRES_EXACT_GR", "A quasi-regime or candidate is not an Exact PR")
    if m["direction"] in {"POSITIVE", "NEGATIVE"} and m["zero_effect"] != "EXCLUDED":
        fail("SIGN_NONZERO", "A strictly signed effect excludes zero throughout the joint set")
    if m["zero_effect"] == "ALL_ZERO" and m["direction"] != "NOT_APPLICABLE":
        fail("ZERO_DIRECTION", "An identically zero effect has no positive or negative direction")

    empirical_valid = c["validity"] == "VALID" and c["epistemic_mode"] == "EMPIRICAL_CONFIRMATORY"
    if empirical_valid:
        if c["selection_status"] == "POST_HOC_EXPLORATORY":
            fail("POSTHOC_CONFIRMATORY", "Post-hoc exploration cannot be a valid confirmatory application")
        if c["selection_status"] == "FROZEN_REGISTERED" and p["registration_ref"] is None:
            fail("REGISTRATION_EVIDENCE", "Supply the declared external freeze/registration record")
        if c["provenance_status"] != "SUPPORTED":
            fail("EMPIRICAL_PROVENANCE", "A valid confirmatory application must declare supported provenance")
        if r["class"] == "EXACT_GR" and r["descriptor_nondegenerate"] is not True:
            fail("CONFIRMATORY_NONDEGENERACY", "Confirmatory Exact GR requires descriptor nondegeneracy, not forward richness")
        if substantive == "ROBUST_PR" and not r["grounded"]:
            fail("CONFIRMATORY_GROUNDING", "Confirmatory PR must be grounded")
    if selected is not None and c["epistemic_mode"].startswith("EMPIRICAL"):
        if selected["reachable_support"] != "SUPPORTED" or selected["causal_modularity"] != "SUPPORTED":
            if c["identification_status"] != "STRUCTURALLY_UNRESOLVED":
                fail("EMPIRICAL_IDENTIFICATION", "Unresolved support/modularity must remain structurally unresolved")
    return report()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bundle", type=Path, help="Path to application.json")
    parser.add_argument("--json", action="store_true", help="Emit machine-readable validation result")
    parser.add_argument("--digest", action="store_true", help="Print the proposed digest; never modifies files")
    args = parser.parse_args(argv)
    try:
        document = load_json(args.bundle)
        result = validate_document(document, args.bundle.parent)
        proposed_digest = None
        if args.digest:
            # Bootstrap permits matching placeholder/stale IDs, not a broken
            # certificate-to-pipeline link. Every other error remains fatal.
            other = [e for e in result["errors"] if e["code"] != "PIPELINE_DIGEST"]
            if not other:
                proposed_digest = pipeline_digest(document)
            # Generation success is separate from validation of the input IDs.
            # Preserve PIPELINE_DIGEST and contract_valid=False during bootstrap.
            result["digest_generated"] = proposed_digest is not None
            result["proposed_pipeline_id"] = proposed_digest
        if args.json:
            print(json.dumps(result, indent=2, sort_keys=True, allow_nan=False))
        elif proposed_digest is not None:
            print(proposed_digest)
        else:
            print("CONTRACT PASS" if result["contract_valid"] else "CONTRACT FAIL")
            for error in result["errors"]:
                print(f"{error['code']}: {error['message']}")
            print(NOTICE)
        return 0 if proposed_digest is not None or result["contract_valid"] else 1
    except (OSError, ValueError, KeyError, RecursionError) as exc:
        result = {"contract_valid": False, "scientific_claims_verified": False,
                  "errors": [{"code": "INPUT_OR_CONFIGURATION", "message": str(exc)}], "notice": NOTICE}
        if args.digest:
            result.update(digest_generated=False, proposed_pipeline_id=None)
        print(json.dumps(result, sort_keys=True) if args.json else f"INPUT ERROR: {exc}")
        return 2


if __name__ == "__main__":
    sys.exit(main())

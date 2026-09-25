"""Rebuild didactic examples, or compare them without modifying frozen files."""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from application.validator.validate_application import pipeline_digest

HERE = Path(__file__).resolve().parent
NAMES = ("exact_gr_minimal", "grounded_pr_minimal", "quasi_regime_minimal",
         "unresolved_identification", "invalid_posthoc_specification",
         "valid_posthoc_exploratory", "invalid_application_record")
SPEC = """# Didactic finite model (not an empirical application)

These fixtures demonstrate contract syntax. All timestamps, evidence records and
empirical-mode flags in fixtures are synthetic; they do not certify real data.

## Typed state, sufficiency and primitives
S={*}, X={0,1}, A={0,1}; all actions feasible. The full state is Markov.
alpha selects a=1-x, P gives x'=a, and U retains *. Components are alpha, P, U
and feasibility. No further hard identity forces a target expansion.

## Regime and relevant observables
B=B0=B1=S x {0,1}; h(*,x)=x; g(*,x)=x. The descriptor space is discrete {0,1}.
nu assigns 1/2 to each point. Convergence mode: almost-sure weak convergence of
empirical occupation measures, for every initial probability on B0.
The baseline descriptor law varies across the basin and remains forward-active.

## Property, intervention and target transport
psi(mu) is c when the occupation mean of x converges to the deterministic
constant c, mu-almost surely; otherwise psi(mu)=0. Thus psi is a property of
path laws, not an unrecorded sample-path statistic.
The metric is absolute difference. J0 replaces alpha by the constant action 0;
P, U and feasibility are held fixed. Target grammar: atomic alpha component;
its hard target closure is itself. No quotient/reparameterization is used;
semantic transport is identity and the schedule is stationary (no clock needed).

## Model set and inference procedure
The formal model set is the singleton model defined here; comparison covers both
B1 states, not a sampled majority. There is no sampling uncertainty in this model.
The effect convention is intervention minus baseline. Bounds are exact rationals.
A ROOT node declares these model primitives; it is not empirical source evidence.
"""
ARGUMENT = """# Analytic argument for the didactic example

The two baseline world states alternate forever, so B is invariant. For either
initial state, the occupation fraction of state 1 differs from 1/2 by at most
1/(2T) for T>=1. Therefore it converges to 1/2 on every path, also under every
mixture of the two point initial laws. This gives the stated Exact GR.

Under J0 the next world state is 0 and stays 0. Its occupation mean is zero
from either initial state, whereas the baseline mean is 1/2. Thus the signed
effect is -1/2 and the absolute uniform gap is 1/2 on all of B1. B, h and psi
factor through the declared world projection g. No new Lean theorem is claimed.

The argument is an analytic worked example, not output from the JSON validator.
"""
QUASI = """# Didactic leaky model (not an empirical application)

S={*}, X={0,1,2}, A={0,1}, all actions feasible; alpha chooses 1-x on x=0,1
and 0 at x=2. P moves from x=0,1 to action a with probability 99/100 and to
2 with probability 1/100. State 2 is absorbing. U retains *. The full state is
Markov. Components alpha, P, U and feasibility have no hard target coupling.

B=B0={(*,0),(*,1)}, h(*,x)=x globally (including the exit state 2). The question
is finite survival for L=10 and eta=1/10. There is no limiting-law claim, no
convergence-mode claim, no constitutive comparison and no QSD claim. Relevance
and comparison bindings are NOT_APPLICABLE. The grammar has the four primitives;
no intervention or reparameterization is evaluated. Transport is identity.

The model set is the singleton specified model; there is no sampling. Killed
survival from either state is (99/100)^10 >= 1-10/100 = 9/10, by Bernoulli's
inequality. This proves the finite-persistence gate; it does not prove Exact GR.
"""
UNRESOLVED = """# Synthetic unresolved-record illustration

This is NOT empirical evidence. It is a serialization example for an application
whose candidate B, basin, descriptor and proposed J0 are declared using the finite
model vocabulary, but whose true mechanisms are not identified. The state model
is an assumption only; Exact GR and occupation convergence are not established.
The frozen model-set rule retains all support/modularity-compatible completions,
including zero effects. The reported outer set is incomplete, not an average or
intersection of per-model estimates. Direction and uniform gap remain unresolved.
The hypothetical statistical procedure has not established simultaneous coverage.
All empirical assertions here are placeholders for an actual future evidentiary
record and the certificate must remain unresolved, not ROBUST_PR.
"""


def encoded(value: object) -> str:
    return json.dumps(value, indent=2, ensure_ascii=True, allow_nan=False) + "\n"


def make_example(name: str) -> dict[str, str]:
    contents = {"specification.md": SPEC, "argument.md": ARGUMENT}
    bindings = {k: "spec" for k in (
        "typed_state", "state_sufficiency", "action_selection", "world_transition",
        "strategic_update", "feasible_actions", "regime_region", "initial_basin",
        "descriptor", "limiting_law", "convergence_mode", "relevance_map",
        "property_map", "comparison_set", "component_grammar", "hard_structural_relations",
        "semantic_transport_rules", "model_set_rule", "inference_procedure")}
    bindings["clock_state"] = None
    pipeline = {"pipeline_id": "sha256:" + "0" * 64, "bindings": bindings,
        "components": [{"id": key, "kind": kind} for key, kind in (
            ("alpha", "ACTION_SELECTION"), ("P", "WORLD_TRANSITION"),
            ("U", "STRATEGIC_UPDATE"), ("feasibility", "FEASIBILITY"))],
        "selection_status": "FROZEN_REGISTERED", "frozen_at": "2026-09-01T00:00:00Z",
        "evaluation_started_at": "2026-09-02T00:00:00Z",
        "registration_ref": None, "selection_adjustment_ref": None}
    intervention = {"id": "J0", "type": "ACTION_SELECTION", "target_form": "ATOMIC",
        "target_components": ["alpha"], "effective_target_components": ["alpha"],
        "held_fixed_components": ["P", "U", "feasibility"], "replacement_ref": "spec",
        "hard_target_closure_ref": "spec", "schedule": "STATIONARY",
        "formal_admissibility": "ADMISSIBLE", "reachable_support": "NOT_APPLICABLE",
        "causal_modularity": "NOT_APPLICABLE"}
    cert = {"validity": "VALID", "epistemic_mode": "FORMAL_THEORETICAL",
        "selection_status": "FROZEN_REGISTERED", "identification_status": "POINT_IDENTIFIED",
        "statistical_status": "NOT_APPLICABLE", "provenance_status": "NOT_APPLICABLE",
        "substantive_pr_status": "ROBUST_PR", "direction_status": "NEGATIVE",
        "uniform_gap_status": "ESTABLISHED", "pipeline_id": pipeline["pipeline_id"],
        "scope": "FROZEN_PROTOCOL", "intervention_id": "J0", "claim_refs": ["effect"]}
    model_set = {"id": "M", "kind": "POINT_IDENTIFIED", "nonempty": True,
        "rule_ref": "spec", "inference_procedure_ref": "spec", "comparison_set_ref": "spec",
        "quantification": "ALL_MODELS_ALL_COMPARISON_STATES", "sampling_applicable": False,
        "coverage": "NOT_APPLICABLE", "zero_effect": "EXCLUDED", "direction": "NEGATIVE",
        "uniform_gap": {"status": "ESTABLISHED", "lower_bound": "1/2", "claim_refs": ["effect"]},
        "claim_refs": ["effect"]}
    regime = {"class": "EXACT_GR", "exactness_basis": "ANALYTIC",
        "descriptor_nondegenerate": True, "grounded": True, "forward_richness": "FORWARD_ACTIVE",
        "horizon": None, "eta": None, "qsd_claim_id": None, "claim_refs": ["regime"]}
    nodes = [{"id": "primitives", "kind": "DECLARED_IDENTITY_OR_AXIOM", "artifact_ref": "spec",
              "depends_on": [], "description": "Declared synthetic model primitives; no empirical warrant."},
             {"id": "regime", "kind": "CLAIM", "artifact_ref": "argument", "depends_on": ["primitives"],
              "description": "Analytic regime argument, independently readable in the artifact."},
             {"id": "effect", "kind": "CLAIM", "artifact_ref": "argument", "depends_on": ["primitives"],
              "description": "Analytic effect argument; not machine-proved by this validator."}]
    doc = {"standard_version": "0.1.0", "compatible_theory": "0.1.8", "application_id": name,
        "artifacts": [], "regime": regime, "semantic_pipeline": pipeline,
        "interventions": [intervention], "provenance_graph": {"nodes": nodes},
        "identified_set": model_set, "certificate": cert}
    if name in {"exact_gr_minimal", "quasi_regime_minimal"}:
        doc["interventions"] = []
        cert.update(substantive_pr_status="NOT_EVALUATED", direction_status="NOT_APPLICABLE",
                    uniform_gap_status="NOT_APPLICABLE", intervention_id=None, claim_refs=[])
        model_set.update(zero_effect="NOT_ASSESSED", direction="NOT_APPLICABLE", comparison_set_ref=None,
                         quantification="NOT_EVALUATED", claim_refs=[])
        model_set["uniform_gap"] = {"status": "NOT_APPLICABLE", "lower_bound": None, "claim_refs": []}
        bindings["property_map"] = bindings["comparison_set"] = None
        nodes.pop()
    if name == "quasi_regime_minimal":
        contents = {"specification.md": QUASI, "argument.md": QUASI}
        bindings["limiting_law"] = bindings["convergence_mode"] = bindings["relevance_map"] = None
        regime.update(**{"class": "QUASI_REGIME", "exactness_basis": "NOT_ESTABLISHED",
                         "grounded": False, "horizon": 10, "eta": 0.1})
    if name == "unresolved_identification":
        contents["argument.md"] = UNRESOLVED
        regime.update(**{"class": "CANDIDATE", "exactness_basis": "NOT_ESTABLISHED",
                         "descriptor_nondegenerate": None, "grounded": False,
                         "forward_richness": "NOT_ASSESSED", "claim_refs": []})
        bindings["limiting_law"] = bindings["convergence_mode"] = None
        pipeline["selection_status"] = "POST_HOC_EXPLORATORY"
        cert.update(epistemic_mode="EMPIRICAL_EXPLORATORY", selection_status="POST_HOC_EXPLORATORY",
                    identification_status="STRUCTURALLY_UNRESOLVED", statistical_status="STATISTICALLY_UNRESOLVED",
                    provenance_status="INSUFFICIENT", substantive_pr_status="PR_STATUS_AMBIGUOUS",
                    direction_status="DIRECTION_AMBIGUOUS", uniform_gap_status="UNRESOLVED")
        model_set.update(kind="STRUCTURALLY_UNRESOLVED", quantification="INCOMPLETE", zero_effect="POSSIBLE",
                         direction="DIRECTION_AMBIGUOUS", sampling_applicable=True, coverage="UNRESOLVED")
        model_set["uniform_gap"] = {"status": "UNRESOLVED", "lower_bound": None, "claim_refs": []}
        intervention.update(reachable_support="UNRESOLVED", causal_modularity="UNRESOLVED")
    if name in {"invalid_posthoc_specification", "valid_posthoc_exploratory", "invalid_application_record"}:
        pipeline.update(selection_status="POST_HOC_EXPLORATORY", frozen_at="2026-09-03T00:00:00Z")
        cert.update(selection_status="POST_HOC_EXPLORATORY", epistemic_mode="EMPIRICAL_CONFIRMATORY", provenance_status="SUPPORTED")
        intervention.update(reachable_support="SUPPORTED", causal_modularity="SUPPORTED")
        if name == "valid_posthoc_exploratory":
            cert["epistemic_mode"] = "EMPIRICAL_EXPLORATORY"
        if name == "invalid_application_record":
            cert["validity"] = "INVALID"
    ids = {"specification.md": "spec", "argument.md": "argument"}
    doc["artifacts"] = [{"id": ids[path], "path": path, "sha256": hashlib.sha256(data.encode()).hexdigest()}
                        for path, data in contents.items()]
    digest = pipeline_digest(doc)
    pipeline["pipeline_id"] = cert["pipeline_id"] = digest
    contents["application.json"] = encoded(doc)
    return contents


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Explicitly regenerate committed fixtures")
    args = parser.parse_args()
    failures = []
    for name in NAMES:
        for relative, content in make_example(name).items():
            path = HERE / name / relative
            if args.write:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content, encoding="utf-8", newline="\n")
            elif not path.is_file() or path.read_text(encoding="utf-8") != content:
                failures.append(str(path.relative_to(ROOT)))
    expected = {name: ([] if name != "invalid_posthoc_specification" else ["POSTHOC_CONFIRMATORY"]) for name in NAMES}
    path = HERE / "expectations.json"
    if args.write:
        path.write_text(encoded(expected), encoding="utf-8", newline="\n")
    elif not path.is_file() or path.read_text(encoding="utf-8") != encoded(expected):
        failures.append(str(path.relative_to(ROOT)))
    for failure in failures:
        print("DRIFT", failure)
    print("Example regeneration " + ("FAIL" if failures else "PASS"))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())

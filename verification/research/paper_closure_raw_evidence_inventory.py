"""Preserve raw audit source/output bytes and distinguish their hash fields."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research/paper_closures"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def preserve(source, destination):
    payload = source.read_bytes()
    if destination.exists() and destination.read_bytes() != payload:
        raise RuntimeError("Refusing to overwrite a different durable raw file: " + str(destination))
    destination.write_bytes(payload)
    return {"original": source.relative_to(ROOT).as_posix(),
            "durable": destination.relative_to(ROOT).as_posix(), "sha256": sha(destination)}


def main():
    # Keep the measured Windows bytes independently of Git's text conversion
    # on the older verification directory. Historical owner receipts stay put.
    receipt_copies = []
    durable = {}
    for original in sorted((ROOT / 'verification/research').glob('paper_closure_*_receipt_2026-10-18.json')):
        stem = original.name.removeprefix('paper_closure_').removesuffix('_receipt_2026-10-18.json')
        destination = OUT / (stem + '_audit_receipt.json')
        if destination.exists():
            if json.loads(destination.read_text(encoding='utf-8-sig')) != json.loads(original.read_text(encoding='utf-8-sig')):
                raise RuntimeError('Refusing a semantically different owner receipt: '+str(original))
        else:
            destination.write_bytes(original.read_bytes())
        durable[stem] = destination
        receipt_copies.append({'owner_path': original.relative_to(ROOT).as_posix(),
                               'durable': destination.relative_to(ROOT).as_posix(),
                               'sha256': sha(destination)})
    rows = []
    pairs = [
        ("economic", "EconomicWitnessAxiomAudit", "economic"),
        ("finite_transport", "FiniteTransportAxiomAudit", "finite_transport"),
        ("full_path_product", "FullPathProductAxiomAudit", "full_path_product"),
        ("nonfinite_counterexample", "NonfiniteCounterexampleAxiomAudit", "nonfinite_counterexample"),
        ("regenerative", "RegenerativeFactorizationAxiomAudit", "regenerative"),
        ("regenerative_moment", "RegenerativeMomentAxiomAudit", "regenerative_moment"),
        ("strategy", "StrategyAxiomAudit", "strategy"),
    ]
    for unit, stem, receipt_stem in pairs:
        receipt = durable[receipt_stem]
        data = json.loads(receipt.read_text(encoding="utf-8-sig"))
        source = ROOT / (".lake/closure-build/" + stem + ".lean")
        stdout = source.with_suffix(".out")
        if sha(source) != data["audit_source_sha256"] or sha(stdout) != data["audit_stdout_sha256"]:
            raise RuntimeError("Actual raw bytes do not match receipt fields: " + unit)
        rows.append({"unit": unit, "receipt": receipt.relative_to(ROOT).as_posix(),
                     "receipt_sha256": sha(receipt),
                     "audit_source": preserve(source, OUT / (unit + "_audit_source.lean.txt")),
                     "audit_stdout": preserve(stdout, OUT / (unit + "_signatures_axioms.txt")),
                     "field_meanings": {"audit_source_sha256": "generated Lean audit source bytes",
                                        "audit_stdout_sha256": "compiler stdout/stderr bytes"}})
    receipt = OUT / "belief_receipt.json"
    data = json.loads(receipt.read_text(encoding="utf-8-sig"))
    source = ROOT / ".lake/belief-paper-closure/axiom_audit.lean"
    stdout = source.with_suffix(".out")
    if sha(source) != data["audit_sha256"]:
        raise RuntimeError("Belief generated audit source does not match audit_sha256")
    rows.append({"unit": "belief", "receipt": receipt.relative_to(ROOT).as_posix(),
                 "receipt_sha256": sha(receipt),
                 "audit_source": preserve(source, OUT / "belief_audit_source.lean.txt"),
                 "audit_stdout": preserve(stdout, OUT / "belief_signatures_axioms.txt"),
                 "field_meanings": {"audit_sha256": "generated Lean audit source bytes, not stdout"},
                 "definition": "verification/research/audit_belief_closure.py assigns digest(audit) before invoking Lean"})
    receipt = OUT / 'measurable_nat_clock_receipt.json'
    data = json.loads(receipt.read_text(encoding='utf-8-sig'))
    source = ROOT / '.lake/closure-build/MeasurableNatClockAxiomAudit.lean'
    stdout = source.with_suffix('.out')
    if sha(stdout) != data['audit_stdout_sha256']:
        raise RuntimeError('General measurable clock stdout differs from its receipt')
    rows.append({'unit': 'measurable_nat_clock', 'receipt': receipt.relative_to(ROOT).as_posix(),
                 'receipt_sha256': sha(receipt),
                 'audit_source': preserve(source, OUT/'measurable_nat_clock_audit_source.lean.txt'),
                 'audit_stdout': preserve(stdout, OUT/'measurable_nat_clock_audit_stdout.txt'),
                 'field_meanings': {'audit_stdout_sha256': 'compiler stdout/stderr bytes'},
                 'audit_source_hash_origin': 'Independent raw preservation; no audit-source hash field is claimed in the owner receipt'})
    inventory = {"format": "Permansson.RawAuditEvidenceInventory.v1", "status": "PASS",
                 "interpretation": "Raw byte copies; audit source and compiler output have distinct hashes. No owner receipt was changed.",
                 "builder_sha256": sha(Path(__file__)), "durable_owner_receipts": receipt_copies,
                 "audits": rows}
    (OUT / "acceptance_raw_evidence_inventory.json").write_text(
        json.dumps(inventory, indent=2) + "\n", encoding="utf-8")
    print("Raw evidence inventory PASS:", len(rows), "audit source/output pairs")


if __name__ == "__main__":
    main()

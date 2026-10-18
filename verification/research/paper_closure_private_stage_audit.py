"""Source-bound signatures and actual transitive axioms for private-control LP.

The shared auditor checks the pinned compiler, recompiles missing or stale
artifacts, and audits every named public export in the three new modules.
"""
import paper_closure_analytic_audit as audit

audit.AUDIT_STEM = "PrivateControlStageAxiomAudit"
audit.SIGNATURES_BASENAME = "private_control_stage_signatures_axioms.txt"
audit.DEFAULT_OUTPUT = "research/paper_closures/private_control_stage_receipt.json"
audit.MODULES = ["ReverseSolver." + name for name in [
    "PrivateControlStageModel", "PrivateControlStageOptimizer", "PrivateControlStageFixture",
]]

if __name__ == "__main__":
    audit.main()

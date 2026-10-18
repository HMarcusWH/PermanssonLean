"""Source-bound U17 original-predicate and transitive axiom audit."""
import paper_closure_strategy_audit as audit

audit.UNIT = 'U17'
audit.AUDIT_STEM = 'EconomicWitnessAxiomAudit'
audit.OUTPUT = 'verification/research/paper_closure_economic_receipt_2026-10-18.json'
audit.MODULES = [
    'PermanssonResearch/EconomicWitness/' + name + '.lean'
    for name in ['Model', 'Incentives', 'Geometry', 'FullStrategyTrace', 'ExactRegime',
                 'ConstitutionCore', 'Constitution', 'Regression']
]
audit.RESIDUAL = (
    'This is the new three-world witness selected by the 2026-10-18 build specification. '
    'It is not a pre-existing empirical or preregistered model, and it does not reinterpret '
    'historical X1. Behavioral optimality uses expected discounted rewards with the fixed '
    'opponent and nonanticipating independently randomized own action interface. '
    'No uniqueness of equilibrium or empirical adequacy is claimed.'
)

if __name__ == '__main__':
    raise SystemExit(audit.main())

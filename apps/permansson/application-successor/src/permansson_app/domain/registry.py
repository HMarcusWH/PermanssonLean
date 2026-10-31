"""Source-derived artifact paths for six distinct empirical companion families.

Matching on explicit release-local suffixes is evidence discovery, not evidence
that a package implements or validates a mathematical theorem.
"""
from __future__ import annotations
from dataclasses import dataclass
from ..errors import AppError

@dataclass(frozen=True)
class DomainProfile:
    name:str
    required_suffixes:tuple[str,...]
    optional_suffixes:tuple[str,...]=()

PROFILES={
    'russia_ukraine':DomainProfile('russia_ukraine',(
        'reproducibility/FROZEN_ANALYSIS_SPEC_v0.4.1_328.json',
        'reproducibility/inputs/events.csv','reproducibility/state_weekly.csv',
        'reproducibility/transition_hindcast_daily.csv'),(
        'reproducibility/inputs/observability_samples.csv',
        'reproducibility/known_at_delayed_events.csv')),
    'hormuz':DomainProfile('hormuz',(
        'reproducibility/FROZEN_SPEC.json','reproducibility/data/events.csv',
        'reproducibility/outputs/state_weekly.csv'),(
        'predictive_validation/test_2_prospective_freeze/PROSPECTIVE_TEST_2_SPEC.json',)),
    'iran':DomainProfile('iran',(
        'inputs/update_original/iran_v0_2_structured_update_FINAL_AUDIT.json',
        'results/evidence/all_measurements_typed.csv',
        'results/successor/summary.json'),(
        'results/hormuz/REPLAY_SPECIFICATION.json',)),
    'midr':DomainProfile('midr',(
        'specs/MIDR_v1_0_release_spec.json','data/support_gain_matrix.csv',
        'data/transition_semantics.csv','data/claim_ledger.csv'),(
        'data/source_ledger.csv',)),
    'brown_mackay':DomainProfile('brown_mackay',(
        'FROZEN_SPEC.json','primary_results.json',
        'INDEPENDENT_CHECK.json','gate_results.csv'),(
        'continuous_benchmarks.csv',)),
    'cross_conflict':DomainProfile('cross_conflict',(
        '02_cross_conflict_geometry/Cross-conflict_geometry_summary.csv',
        '02_cross_conflict_geometry/PRT_cross_conflict_geometry_weekly.csv',
        '04_refined_sync_test/PRT_refined_sync_test_episodes.csv'),(
        '03_ledger_sanity_check/PRT_cross_conflict_ledger_sanity_verdicts.csv',)),
}


def resolve_profile(name:str)->DomainProfile:
    try:return PROFILES[name]
    except (KeyError,TypeError) as e:raise AppError('DOMAIN_PROFILE','unsupported domain adapter') from e

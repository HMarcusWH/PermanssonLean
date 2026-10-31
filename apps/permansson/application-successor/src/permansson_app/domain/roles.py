"""Explicit evidence role labels; support matrices never become causal kernels."""
from __future__ import annotations
from ..errors import AppError

_ALLOWED={'source','observation','measurement','support','classification','counterfactual',
          'calculation','audit','unknown'}

def validate_role(role:str)->str:
    if type(role) is not str or role not in _ALLOWED:
        raise AppError('DOMAIN_ROLE','unrecognized evidence role')
    return role

def inferred_role(path:str)->str:
    name=path.lower()
    if any(x in name for x in ('sha256','manifest','audit','provenance','validation_report')):
        return 'audit'
    if any(x in name for x in ('support_gain','support_ranking','exposure_scores','leverage_support')):
        return 'support'
    if any(x in name for x in ('counterfactual','scenario','sensitivity','robustness')):
        return 'counterfactual'
    if any(x in name for x in ('source_ledger','sources','claims','events','observability')):
        return 'source'
    if any(x in name for x in ('transition','state_weekly','geometry_weekly','snapshots')):
        return 'measurement'
    if any(x in name for x in ('classification','episode')):
        return 'classification'
    if name.endswith('.csv') or name.endswith('.json'):
        return 'observation'
    return 'unknown'

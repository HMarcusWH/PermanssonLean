"""Frozen, typed comparison semantics. No status can be promoted by labels.

A complete declared starting-state universe is needed to interpret uniform claims.
"""
from __future__ import annotations
from dataclasses import dataclass
from .identity import semantic_identity
from .errors import AppError

_PROPERTIES={'finite_survival','first_exit','occupation','residence','hitting','safety','terminal_reward','stationary_classwise'}
_OBJECTIVES={'maximize','minimize','evaluate_only'}
_COMPARATORS={'exact_equal','positive_margin','weak_dominance','distributional','not_compared'}
_POLICIES={'fixed_alpha','frozen_menu','fully_observed_feedback','observation_history','stationary_randomized'}
_NATURE={'single_model','rectangular_after_action','committed_at_time_zero','private_stage'}

@dataclass(frozen=True)
class SemanticScope:
    property: str
    objective: str
    comparator: str
    policy_class: str
    nature_chronology: str
    horizon: int
    state_universe: tuple[str,...]
    comparison_starts: tuple[str,...]
    mode: str

    @classmethod
    def parse(cls,data:object)->'SemanticScope':
        keys={'property','objective','comparator','policy_class','nature_chronology',
              'horizon','state_universe','comparison_starts','mode'}
        if type(data) is not dict or set(data)!=keys:
            raise AppError('SEMANTICS_SHAPE','semantic scope has missing or extra keys')
        for name,options in [('property',_PROPERTIES),('objective',_OBJECTIVES),
                              ('comparator',_COMPARATORS),('policy_class',_POLICIES),
                              ('nature_chronology',_NATURE)]:
            if type(data[name]) is not str or data[name] not in options:
                raise AppError('SEMANTICS_VALUE','unsupported '+name)
        if data['mode'] not in ('numeric','lean_replay','empirical'):
            raise AppError('SEMANTICS_MODE','unsupported evaluation mode')
        h=data['horizon']
        if type(h) is not int or not 0<=h<=1_000_000:
            raise AppError('SEMANTICS_HORIZON','invalid finite horizon')
        def states(k):
            values=data[k]
            if (type(values) is not list or not values or len(values)>216 or
                any(type(x) is not str or not x or len(x)>80 for x in values) or
                len(values)!=len(set(values))):
                raise AppError('SEMANTICS_STATES','invalid '+k)
            return tuple(values)
        universe=states('state_universe')
        starts=states('comparison_starts')
        if not set(starts).issubset(universe):
            raise AppError('SEMANTICS_STATES','comparison starts not contained in universe')
        if data['comparator']=='not_compared' and data['objective']!='evaluate_only':
            raise AppError('SEMANTICS_COMPARATOR','optimization requires declared comparison semantics')
        return cls(data['property'],data['objective'],data['comparator'],data['policy_class'],
                   data['nature_chronology'],h,universe,starts,data['mode'])

    def to_dict(self)->dict:
        return {'property':self.property,'objective':self.objective,'comparator':self.comparator,
                'policy_class':self.policy_class,'nature_chronology':self.nature_chronology,
                'horizon':self.horizon,'state_universe':list(self.state_universe),
                'comparison_starts':list(self.comparison_starts),'mode':self.mode}

    def identity(self)->dict:
        return semantic_identity('finite-property-and-comparison-scope',self.to_dict())

    def require_full_region(self)->None:
        if set(self.comparison_starts)!=set(self.state_universe):
            raise AppError('SEMANTICS_PARTIAL','uniform claim omitted comparison starting states')


def compare_semantics(expected:SemanticScope,claimed:SemanticScope,*,uniform:bool=False)->dict:
    if type(expected) is not SemanticScope or type(claimed) is not SemanticScope or expected!=claimed:
        raise AppError('SEMANTICS_MISMATCH','scope, chronology, model, or comparator changed')
    if uniform:expected.require_full_region()
    return {'status':'SCOPE_MATCH','source_authenticated':False,
            'mathematical_certification':False,'semantic_identity':expected.identity()}

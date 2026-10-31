"""Independent exact consumer-side checker for finite nature chronology receipts.

No producer import: recomposes action/nature rows from the authenticated typed
input and checks every chronological recurrence, every tie and fixed-policy
comparison. It is not a Lean proof or an independent scientific certification.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..identity import canonical_bytes, rational_text
from ..engines.robust_nature import parse_nature, RECEIPT, MAX_RESULT_BITS


def _same(got, expected, name='receipt'):
    """Check exact JSON structure, scalar types and values; bool != int."""
    if type(got) is not type(expected):
        raise AppError('NATURE_RECEIPT', name+' type mismatch')
    if type(expected) is dict:
        if set(got) != set(expected):
            raise AppError('NATURE_RECEIPT', name+' key mismatch')
        for key in expected:
            _same(got[key],expected[key],name+'.'+key)
    elif type(expected) is list:
        if len(got)!=len(expected):
            raise AppError('NATURE_RECEIPT', name+' array length mismatch')
        for i,(g,e) in enumerate(zip(got,expected)):
            _same(g,e,name+'['+str(i)+']')
    elif got != expected:
        raise AppError('NATURE_RECEIPT', name+' value mismatch')


def check_nature(raw:object, receipt:object)->dict:
    q=parse_nature(raw)
    N=len(q.states); M=len(q.nature_ids)
    # Independently build all action-conditioned stochastic matrices. No use of
    # producer's row helper, value routine or memoized candidate outputs.
    matrices=[]
    for model in q.nature_worlds:
        by_action=[]
        for s,x in q.states:
            choices={}
            for a in q.baseline.feasible[s,x]:
                values=[]
                for ss,xx in q.states:
                    pos=model.world.index(xx)
                    strategy=model.strategic.index(ss)
                    values.append(model.P[s,x,a][pos]*model.U[s,x,a,xx][strategy])
                if sum(values,Fraction(0))!=1:
                    raise AppError('NATURE_RECEIPT','nonstochastic actual P/U row')
                choices[a]=tuple(values)
            by_action.append(choices)
        matrices.append(by_action)

    zero=[q.rewards]
    rect=[q.rewards]
    scenario=[[q.rewards] for _ in range(M)]
    argmax=[[[] for _ in range(N)]]
    argmin=[[{} for _ in range(N)]]
    nature_min_fixed=[[[] for _ in range(N)]]

    for remaining in range(1,q.horizon+1):
        rect_row=[];optim_row=[];opt_actions=[];nature_by_action=[];nature_fixed=[]
        for state in range(N):
            payoffs={}
            minimizers={}
            for action in q.baseline.feasible[q.states[state]]:
                actions=[]
                for theta in range(M):
                    probabilities=matrices[theta][state][action]
                    actions.append(sum((probabilities[j]*zero[-1][j] for j in range(N)),Fraction(0)))
                val=min(actions)
                payoffs[action]=val
                minimizers[action]=[q.nature_ids[k] for k in range(M) if actions[k]==val]
            best=max(payoffs.values())
            opt_actions.append([action for action,value in payoffs.items() if value==best])
            nature_by_action.append(minimizers)
            optim_row.append(best)
            fixed=q.policy[state]
            scores=[sum((matrices[k][state][fixed][j]*rect[-1][j] for j in range(N)),Fraction(0)) for k in range(M)]
            rect_row.append(min(scores))
            nature_fixed.append([q.nature_ids[k] for k in range(M) if scores[k]==min(scores)])
        if any(max(v.numerator.bit_length(),v.denominator.bit_length())>MAX_RESULT_BITS for v in (*rect_row,*optim_row)):
            raise AppError('NATURE_RESOURCE','independent recurrence rational precision exceeded')
        zero.append(tuple(optim_row));rect.append(tuple(rect_row))
        argmax.append(opt_actions);argmin.append(nature_by_action);nature_min_fixed.append(nature_fixed)
        for k in range(M):
            new=[]
            for state in range(N):
                new.append(sum((matrices[k][state][q.policy[state]][j]*scenario[k][-1][j] for j in range(N)), Fraction(0)))
            if any(max(v.numerator.bit_length(),v.denominator.bit_length())>MAX_RESULT_BITS for v in new):
                raise AppError('NATURE_RESOURCE','independent committed rational precision exceeded')
            scenario[k].append(tuple(new))

    as_text=lambda table:[[rational_text(v) for v in row] for row in table]
    rect_last=tuple(rect[-1][i] for i in q.starts)
    committed_min=tuple(min(scenario[k][-1][i] for k in range(M)) for i in q.starts)
    if any(a>b for a,b in zip(rect_last,committed_min)):
        raise AppError('NATURE_RECEIPT','rectangular fixed policy exceeds committed fixed-policy value')
    if any(zero[-1][i] < rect[-1][i] for i in q.starts):
        raise AppError('NATURE_RECEIPT','optimized rectangular controller below its fixed policy')
    expectation={
        'format':RECEIPT,
        'request_identity':q.identity,
        'baseline_identity':q.baseline.semantic_id(),
        'nature_ids':list(q.nature_ids),
        'nature_model_identities':[model.semantic_id() for model in q.nature_worlds],
        'joint_states':[{'s':s,'x':x} for s,x in q.states],
        'comparison_indices':list(q.starts),
        'horizon':q.horizon,
        'terminal_rewards':[rational_text(v) for v in q.rewards],
        'fixed_policy_actions':list(q.policy),
        'rectangular_optimal_values_by_remaining':as_text(zero),
        'rectangular_argmax_by_remaining':argmax,
        'rectangular_minimizers_by_action':argmin,
        'fixed_policy_rectangular_values_by_remaining':as_text(rect),
        'fixed_policy_rectangular_minimizers':nature_min_fixed,
        'fixed_policy_committed_values_by_nature':[as_text(table) for table in scenario],
        'comparison':{
            'fixed_rectangular':[rational_text(v) for v in rect_last],
            'fixed_committed_worst':[rational_text(v) for v in committed_min],
            'fixed_rectangular_minus_committed':[rational_text(a-b) for a,b in zip(rect_last,committed_min)],
            'rectangular_optimized':[rational_text(zero[-1][i]) for i in q.starts],
        },
        'policy_class':'fully_observed_deterministic_remaining_horizon_rectangular_and_fixed_stationary_for_committed',
        'nature_timing':'after_realized_control_independent_row_reselection_vs_one_model_committed_at_time_zero',
        'committed_scope':'declared_fixed_policy_only_not_committed_game_optimum',
        'strategic_alpha_and_U_held_fixed':True,
        'lean_status':'NOT_EXECUTED',
        'empirical_identification':'NOT_IDENTIFIED',
        'scientific_claims_verified':False,
    }
    _same(receipt, expectation)
    return {'format':'Permansson.App.IndependentNatureChronologyCheck.v1',
            'status':'PASS','checked_states':N,'checked_scenarios':M,
            'checked_horizons':q.horizon+1,
            'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'bound_checked':'rectangular_fixed_policy_value_le_committed_fixed_policy_value_and_optimized_ge_fixed',
            'proof_status':'NOT_EXECUTED','claim_status':'FINITE_RATIONAL_NUMERIC_ONLY'}

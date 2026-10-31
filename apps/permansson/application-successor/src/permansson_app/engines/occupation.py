"""Exact finite recurrent classes and *random* limiting occupation laws.

The absorption-weighted mean law is kept distinct from the realized random law.
An analytic finite-chain result is not an identified empirical GR/PR certificate.
"""
from __future__ import annotations
from fractions import Fraction
from ..errors import AppError
from ..finite_world import FiniteWorld, induced_kernel
from ..identity import rational_text
from .rational_linear import solve_unique


def bottom_classes(K: tuple[tuple[Fraction,...],...]):
    n = len(K)
    if n < 1 or n > 36 or any(len(row) != n for row in K):
        raise AppError('OCCUPATION_DIM','matrix must have between 1 and 36 states')
    adj = [tuple(j for j, p in enumerate(row) if p > 0) for row in K]
    index, stack, onstack, low, order, components = 0, [], set(), {}, {}, []
    def visit(v):
        nonlocal index
        order[v] = low[v] = index; index += 1
        stack.append(v); onstack.add(v)
        for w in adj[v]:
            if w not in order:
                visit(w); low[v] = min(low[v], low[w])
            elif w in onstack:
                low[v] = min(low[v], order[w])
        if low[v] == order[v]:
            component=[]
            while True:
                w = stack.pop(); onstack.remove(w); component.append(w)
                if w == v: break
            components.append(tuple(sorted(component)))
    for v in range(n):
        if v not in order: visit(v)
    classes=[c for c in components if all(j in c for i in c for j in adj[i])]
    return tuple(sorted(classes, key=lambda c: c[0]))


def _stationary(K, states):
    # Solve (pi P) = pi on each closed irreducible class.
    m = len(states)
    A = [[(int(i == j) - K[states[j]][states[i]]) for j in range(m)]
         for i in range(m)]
    A[-1] = [Fraction(1)] * m
    b = [Fraction(0)] * (m - 1) + [Fraction(1)]
    law = solve_unique(A,b)
    if any(p <= 0 for p in law) or sum(law) != 1:
        raise AppError('OCCUPATION_ERROR','invalid closed-class stationary law')
    return law


def compute_occupation(model: FiniteWorld) -> dict:
    K = induced_kernel(model)
    n=len(K)
    classes=bottom_classes(K)
    closed={i for c in classes for i in c}
    transient=[i for i in range(n) if i not in closed]
    laws=[_stationary(K,c) for c in classes]
    absorbing=[]
    for class_index,c in enumerate(classes):
        weights=[Fraction(int(i in c)) for i in range(n)]
        if transient:
            A=[[Fraction(int(i==j))-K[i][j] for j in transient] for i in transient]
            b=[sum((K[i][j] for j in c),Fraction(0)) for i in transient]
            for i,x in zip(transient,solve_unique(A,b)): weights[i]=x
        absorbing.append(tuple(weights))
    if any(sum(absorbing[j][i] for j in range(len(classes))) != 1 for i in range(n)):
        raise AppError('OCCUPATION_ERROR','absorption weights fail mass conservation')
    mean=[]
    for i in range(n):
        row=[]
        for state in range(n):
            row.append(sum((absorbing[j][i]*laws[j][c.index(state)] for j,c in enumerate(classes) if state in c),Fraction(0)))
        mean.append(tuple(row))
    return {
        'format':'Permansson.App.FiniteOccupationReceipt.v1',
        'model_semantic_identity':model.semantic_id(),
        'joint_states':[{'strategic':s,'world':x} for s in model.strategic for x in model.world],
        'bottom_classes':[list(c) for c in classes],
        'stationary_laws':[[rational_text(p) for p in law] for law in laws],
        'absorption_weights':[[rational_text(absorbing[j][i]) for j in range(len(classes))] for i in range(n)],
        'expected_limit_laws':[[rational_text(p) for p in row] for row in mean],
        'limit_interpretation':'RANDOM_CLASS_STATIONARY_LAW_NOT_ITS_MEAN',
        'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
        'scientific_claims_verified':False,
    }

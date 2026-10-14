"""Independent exact-rational receipt validator for C10 reference arithmetic.

The checker does not invert a matrix and does not call the producer's
absorption/event/optimization functions. It independently enumerates SCCs
using DFS and checks every Dirichlet boundary equation, the exact class
partition and the global maximin certificate. This is an independent Python
check, NOT a compiled proof of Lean soundness or JSON parser verification.
"""
from __future__ import annotations
from fractions import Fraction as F
import hashlib, json
import argparse
from typing import Any
from c10_exact_execution import check_input, exact_fraction, canonical_bytes, strict_object

class ReceiptError(ValueError):
    pass


def require(test, message):
    if not test:
        raise ReceiptError(message)


def dfs_edges(matrix, src):
    n=len(matrix)
    seen={src}
    todo=[src]
    while todo:
        x=todo.pop()
        for y in range(n):
            if matrix[x][y]>0 and y not in seen:
                seen.add(y)
                todo.append(y)
    return seen


def independent_classes(matrix):
    n=len(matrix)
    reach=[dfs_edges(matrix,i) for i in range(n)]
    unseen=set(range(n))
    components=[]
    while unseen:
        x=min(unseen)
        c=set(y for y in range(n) if y in reach[x] and x in reach[y])
        unseen-=c
        components.append(c)
    result=[tuple(sorted(c)) for c in components if all(matrix[i][j] == 0 or j in c for i in c for j in range(n))]
    return tuple(sorted(result, key=lambda c:c[0]))


def verify_geometry(matrix, descriptor, proposed):
    require(isinstance(proposed,dict) and set(proposed)=={'classes','absorption','good','event'},'geometry keys')
    classes=independent_classes(matrix)
    require(proposed['classes']==[list(c) for c in classes], 'bottom classes incomplete/wrong or reordered')
    n=len(matrix)
    r=len(classes)
    require(isinstance(proposed['absorption'],list) and len(proposed['absorption'])==r,'absorption column count')
    recurrent=set().union(*[set(c) for c in classes])
    weights=[]
    for j,c in enumerate(classes):
        raw=proposed['absorption'][j]
        require(isinstance(raw,list) and len(raw)==n,'absorption state count')
        p=[exact_fraction(x) for x in raw]
        for x in range(n):
            require(0<=p[x]<=1,'absorption probability outside [0,1]')
            if x in recurrent:
                require(p[x]==(F(1) if x in c else F(0)),'invalid recurrent boundary condition')
            else:
                require(p[x]==sum((matrix[x][y]*p[y] for y in range(n)),F(0)), 'invalid harmonic equation')
        weights.append(p)
    for i in range(n):
        require(sum((w[i] for w in weights),F(0))==F(1),'absorption columns not normalized')
    computed_good=[all(descriptor[i] for i in c) for c in classes]
    require(computed_good==proposed['good'],'incorrect all-true class labeling')
    computed_event=[sum((weights[j][i] for j,g in enumerate(computed_good) if g),F(0)) for i in range(n)]
    require(proposed['event']==[str(v) for v in computed_event],'event probabilities incorrect')
    return computed_event


def verify_receipt(receipt:Any)->bool:
    require(isinstance(receipt,dict),'receipt object')
    require(set(receipt)=={'format','normalized_input','input_sha256','baseline','members','optimum','ties','selected','numerical_status','claim_boundary'},'receipt fields changed')
    fmt = receipt.get('format')
    require(fmt in {'Permansson.C10.rational-margin.v1',
                    'Permansson.C10.rational-margin.v2'}, 'format')
    modern = fmt.endswith('.v2')
    checked=check_input(receipt['normalized_input'])
    require(receipt['normalized_input']==checked.canonical(),'input not canonical/normalized')
    require(receipt['input_sha256']==hashlib.sha256(canonical_bytes(checked.canonical())).hexdigest(),'input fingerprint mismatch')
    basevals=verify_geometry(checked.baseline,checked.descriptor,receipt['baseline'])
    require(isinstance(receipt['members'],list) and len(receipt['members'])==len(checked.menu),'menu cardinality')
    values=[]
    for item,(label,matrix) in zip(receipt['members'],checked.menu):
        expected_fields = {'id', 'geometry', 'effects', 'margin', 'worst_start'}
        if modern:
            expected_fields.add('comparison_effects')
        require(isinstance(item,dict) and set(item)==expected_fields,'member fields')
        require(item['id']==label,'candidate ID/order mismatch')
        probabilities=verify_geometry(matrix,checked.descriptor,item['geometry'])
        full_deltas = [abs(basevals[i]-probabilities[i]) for i in range(checked.n)]
        deltas = [full_deltas[i] for i in checked.comparison]
        if modern:
            require(item['effects'] == [str(d) for d in full_deltas],
                    'complete pointwise effect wrong or truncated')
            require(item['comparison_effects'] == [str(d) for d in deltas],
                    'comparison projection differs from complete vector')
        else:
            require(item['effects'] == [str(d) for d in deltas],
                    'historical v1 comparison effect wrong')
        m=min(deltas)
        require(item['margin']==str(m),'margin not min over all original BR')
        require(item['worst_start']==min(x for x,d in zip(checked.comparison,deltas) if d==m),'wrong argmin start')
        values.append(m)
    optimal=max(values)
    ties=[i for (i,_),v in zip(checked.menu,values) if v==optimal]
    require(receipt['optimum']==str(optimal),'wrong maximin optimum')
    require(receipt['ties']==ties and receipt['selected']==ties[0],'incorrect tie set/order/selection')
    require(receipt['numerical_status']==('NUMERIC_ALL_LISTED_MARGINS_ZERO' if optimal==0 else 'NUMERIC_POSITIVE_BASELINE_UNVERIFIED'),'invalid status')
    require(receipt['claim_boundary']=='Exact rational numerical result only; original typed equality and any positive PR certification require separate Lean theorems.', 'invalid claim boundary')
    return True


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('receipt')
    args=parser.parse_args(argv)
    with open(args.receipt,encoding='utf-8') as f:
        receipt=json.load(f, parse_float=lambda _: (_ for _ in ()).throw(ReceiptError('floating JSON number')), object_pairs_hook=strict_object)
    verify_receipt(receipt)
    print('C10 independent exact-Fraction receipt check PASS (Python, not Lean)')

if __name__=='__main__':
    main()
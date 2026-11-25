"""Local rational kite conversion, not the global MaximinKiteNE algorithm."""
from fractions import Fraction as Q
from .regret import evaluate

def produce(d):
    R,C,x,y,s=(d[k] for k in ("R","C","x","y","epsilon"))
    before=evaluate(R,C,x,y)
    r,c=before["regret"]
    lhs=((1-s)*r+s*c,s*r+(1-s)*c)
    out={"before":before,"threshold":s,"kite_lhs":lhs,"in_kite":max(lhs)<=s}
    if not out["in_kite"]:
        return dict(out,branch="OUTSIDE_KITE",weight=None,output=None)
    t=Q(0)
    branch="UNCHANGED"
    if r>s:
        branch="ROW"
        t=1-s/r
        i=before["best_responses"][0][0]
        x=tuple((1-t)*p+t*(k==i) for k,p in enumerate(x))
    elif c>s:
        branch="COLUMN"
        t=1-s/c
        j=before["best_responses"][1][0]
        y=tuple((1-t)*p+t*(k==j) for k,p in enumerate(y))
    return dict(out,branch=branch,weight=t,
                output={"x":x,"y":y,"evaluation":evaluate(R,C,x,y)})

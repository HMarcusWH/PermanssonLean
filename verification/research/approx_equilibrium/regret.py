"""Exact unilateral incentive calculations for a supplied profile."""
from fractions import Fraction as Q

def evaluate(R,C,x,y):
    r = tuple(sum((R[i][j]*y[j] for j in range(len(y))),Q(0)) for i in range(len(x)))
    c = tuple(sum((C[i][j]*x[i] for i in range(len(x))),Q(0)) for j in range(len(y)))
    u = sum((x[i]*r[i] for i in range(len(x))),Q(0))
    v = sum((y[j]*c[j] for j in range(len(y))),Q(0))
    return {"row_scores":r,"column_scores":c,"payoff":(u,v),
            "regret":(max(r)-u,max(c)-v),
            "best_responses":(tuple(i for i,z in enumerate(r) if z==max(r)),
                              tuple(j for j,z in enumerate(c) if z==max(c)))}

def best_response_projection(p,scores):
    """Move strictly suboptimal mass to the first maximizing action."""
    top=max(scores)
    good=tuple(i for i,z in enumerate(scores) if z==top)
    bad=tuple(i for i,z in enumerate(scores) if z<top)
    mass=sum((p[i] for i in bad),Q(0))
    out=tuple((p[i]+mass if i==good[0] else p[i]) if i in good else Q(0)
              for i in range(len(p)))
    regret=top-sum((a*b for a,b in zip(p,scores)),Q(0))
    gap=min((top-scores[i] for i in bad),default=None)
    return {"best_responses":good,"nonbest_mass":mass,"gap":gap,"projection":out,
            "tv":mass,"bound":min(Q(1),regret/gap) if gap else Q(0)}

def produce(d):
    out=evaluate(d["R"],d["C"],d["x"],d["y"])
    out["epsilon"]=d["epsilon"]
    out["threshold_met"]=max(out["regret"])<=d["epsilon"]
    out["exact_nash"]=max(out["regret"])==0
    out["fixed_opponent_projection"]=(best_response_projection(d["x"],out["row_scores"]),
                                      best_response_projection(d["y"],out["column_scores"]))
    return out

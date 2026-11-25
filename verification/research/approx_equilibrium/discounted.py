"""Exact continuation-game regret and candidate Bellman residuals."""
from fractions import Fraction as Q
from .regret import evaluate

def produce(d):
    n=d["n"]
    rewards=(d["R"],d["C"])
    M=tuple(tuple(tuple(tuple(rewards[i][s][a][b]+d["beta"][i]*
               sum((d["P"][s][a][b][z]*d["V"][i][z] for z in range(n)),Q(0))
               for b in range(2)) for a in range(2)) for s in range(n)) for i in range(2))
    evaluations=tuple(evaluate(M[0][s],M[1][s],d["x"][s],d["y"][s]) for s in range(n))
    rho=tuple(max(abs(d["V"][i][s]-evaluations[s]["payoff"][i]) for s in range(n)) for i in range(2))
    eps=tuple(max(e["regret"][i] for e in evaluations) for i in range(2))
    normalized=[]
    for s in range(n):
        widths=tuple(max(v for r in M[i][s] for v in r)-min(v for r in M[i][s] for v in r)
                     for i in range(2))
        normalized.append({"widths":widths,"regret":tuple(evaluations[s]["regret"][i]/widths[i]
                           if widths[i] else Q(0) for i in range(2))})
    return {"continuation":M,"evaluations":evaluations,"epsilon":eps,"rho":rho,
            "discount":d["beta"],"normalized":normalized,
            "full_history_bound":tuple((eps[i]+2*rho[i])/(1-d["beta"][i]) for i in range(2))}

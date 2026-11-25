"""Emit literal static receipt instances, for the existing real Lean harness."""
from .contract import parse, require
from .checker import check

def rat(q):
    return f"({q.numerator} / {q.denominator} : ℚ)"

def vec(v):
    return "!["+ ", ".join(rat(q) for q in v)+"]"

def mat(m):
    return "!["+ ", ".join(vec(v) for v in m)+"]"

def emit(raw,receipt):
    check(raw,receipt)
    d=parse(raw)
    require(d["kind"]=="regret","only static receipt replay is implemented")
    x,y,R,C=d["x"],d["y"],d["R"],d["C"]
    m,n=len(x),len(y)
    c=tuple(tuple(C[i][j] for i in range(m)) for j in range(n))
    truth=str(receipt["result"]["threshold_met"]).lower()
    return f"""import PermanssonResearch.ApplicationBridge.EquilibriumReceipt
open PermanssonResearch.ApproxEquilibrium
namespace ApproxEquilibriumReplay
def R : Fin {m} → Fin {n} → ℚ := {mat(R)}
def C : Fin {n} → Fin {m} → ℚ := {mat(c)}
def p : Fin {m} → ℚ := {vec(x)}
def q : Fin {n} → ℚ := {vec(y)}
theorem checked : checkNash R C p q {rat(d["epsilon"])} = {truth} := by
  decide +kernel
#print axioms checked
end ApproxEquilibriumReplay
"""

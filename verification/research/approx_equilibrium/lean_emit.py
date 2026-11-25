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

def nested(v):
    if isinstance(v,(tuple,list)):
        return "!["+ ", ".join(nested(q) for q in v)+"]"
    return rat(v)

def emit_discounted(raw,receipt):
    from fractions import Fraction as Q
    check(raw,receipt)
    d=parse(raw)
    require(d["kind"]=="discounted","wrong discounted receipt kind")
    result=receipt["result"]; n=d["n"]
    blocks=["import PermanssonResearch.ApplicationBridge.EquilibriumReceipt",
            "open PermanssonResearch.ApproxEquilibrium",
            "open PermanssonResearch.ApplicationBridge.EquilibriumReceipt",
            "namespace ApproxDiscountedReplay"]
    for i in range(2):
        # Input C and P use global (row,column) order, so transpose BOTH
        # arrays when constructing the second player's own-action-first game.
        rewards=d["R"] if i==0 else tuple(tuple(tuple(d["C"][s][b][a]
            for b in range(2)) for a in range(2)) for s in range(n))
        physical=d["P"] if i==0 else tuple(tuple(tuple(d["P"][s][b][a]
            for b in range(2)) for a in range(2)) for s in range(n))
        own,op=(d["x"],d["y"]) if i==0 else (d["y"],d["x"])
        R=max(abs(v) for m in rewards for row in m for v in row)
        C=max(abs(v) for v in d["V"][i])
        blocks.extend([f"""def model{i} : DiscountedInput {n} where
  player := {i}
  reward := {nested(rewards)}
  physical := {nested(physical)}
  own := {nested(own)}
  opponent := {nested(op)}
  discount := {rat(d["beta"][i])}
  value := {nested(d["V"][i])}
  physical_ok := by decide +kernel
  own_ok := by decide +kernel
  opponent_ok := by decide +kernel
  discount_ok := by decide +kernel

theorem checked{i} : checkDiscounted model{i} {rat(Q(result["epsilon"][i]))} {rat(Q(result["rho"][i]))} {rat(R)} {rat(C)} = true := by
  decide +kernel

#print axioms checked{i}
"""])
    blocks.append("end ApproxDiscountedReplay")
    return "\n".join(blocks)+"\n"

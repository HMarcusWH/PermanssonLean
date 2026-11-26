"""Generate literal checked receipt instances for the real pinned Lean harness.

The generic transport CLI remains numeric-only. The restricted three-state
benchmark has a separate source-bound original-model replay.
"""
from fractions import Fraction as Q
from .contract import parse, require
from .checker import check


def rat(q):
    q=Q(q)
    return f"({q.numerator} / {q.denominator} : ℚ)"


def nested(v):
    if isinstance(v,(tuple,list)):
        return "!["+ ", ".join(nested(q) for q in v)+"]"
    return rat(v)


def mask(n,indices):
    return "!["+ ", ".join("true" if i in indices else "false" for i in range(n))+"]"


def transpose(m):
    return tuple(tuple(m[i][j] for i in range(len(m))) for j in range(len(m[0])))


def render(ns,blocks,targets):
    return "\n\n".join(blocks+["\n".join("#print axioms "+t for t in targets),"end "+ns])+"\n"


def static_defs(d,ns):
    x,y,R,C=(d[k] for k in ("x","y","R","C"))
    m,n=len(x),len(y)
    return ["import PermanssonResearch.ApplicationBridge.EquilibriumReceipt",
            "open PermanssonResearch.ApproxEquilibrium",
            "open PermanssonResearch.ApplicationBridge.EquilibriumReceipt",
            "namespace "+ns,
            f"def R : Fin {m} → Fin {n} → ℚ := {nested(R)}",
            f"def C : Fin {n} → Fin {m} → ℚ := {nested(transpose(C))}",
            f"def p : Fin {m} → ℚ := {nested(x)}",
            f"def q : Fin {n} → ℚ := {nested(y)}"]


def exact_blocks(blocks,targets,e,m,n,tag="",p="p",q="q"):
    for label,M,own,op,size,i in (("Row","R",p,q,m,0),("Column","C",q,p,n,1)):
        name=tag+label
        r=rat(e["regret"][i])
        b="best"+name
        h="checked"+name
        actual="exact"+name
        blocks.extend([
            f"def {b} : Fin {size} → Bool := {mask(size,e['best_responses'][i])}",
            f"theorem {h} : checkExactRegret {M} {own} {op} {r} {b} = true := by\n  decide +kernel",
            f"theorem {actual} : ExactRegretConclusion {M} {own} {op} {r} {b} :=\n  checked_exact_regret {M} {own} {op} {r} {b} {h}"])
        targets.extend((h,actual))


def emit(raw,receipt,*,conclusions=True):
    check(raw,receipt)
    d=parse(raw)
    require(d["kind"]=="regret","wrong static receipt kind")
    e=receipt["result"]
    ns="ApproxEquilibriumReplay"
    blocks=static_defs(d,ns)
    eps=rat(d["epsilon"])
    truth=str(e["threshold_met"]).lower()
    blocks.append(f"theorem checked : checkNash R C p q {eps} = {truth} := by\n  decide +kernel")
    targets=["checked"]
    if conclusions:
        exact_blocks(blocks,targets,e,len(d["x"]),len(d["y"]))
        if e["threshold_met"]:
            blocks.append(f"""theorem actual : ∃ hp : Simplex p, ∃ hq : Simplex q,
    ApproxNash (fun i j => (R i j : ℝ)) (fun j i => (C j i : ℝ))
      (realRow p hp) (realRow q hq) ({eps} : ℝ) :=
  checked_profile R C p q {eps} checked""")
        else:
            blocks.append(f"""theorem actual (hp : Simplex p) (hq : Simplex q) :
    ¬ ApproxNash (fun i j => (R i j : ℝ)) (fun j i => (C j i : ℝ))
      (realRow p hp) (realRow q hq) ({eps} : ℝ) :=
  checked_threshold_failure R C p q {eps} checked hp hq""")
        targets.append("actual")
    return render(ns,blocks,targets)


def emit_kite(raw,receipt,*,conclusions=True):
    check(raw,receipt)
    d=parse(raw)
    require(d["kind"]=="kite","wrong kite receipt kind")
    e=receipt["result"];ns="ApproxKiteReplay"
    blocks=static_defs(d,ns);targets=[]
    m,n=len(d["x"]),len(d["y"])
    s=rat(d["epsilon"]);r,c=(rat(v) for v in e["before"]["regret"])
    if conclusions:
        exact_blocks(blocks,targets,e["before"],m,n,"Before")
    if not e["in_kite"]:
        blocks.append(f"theorem outside : ¬ RationalKite {s} {r} {c} := by\n  decide +kernel")
        targets.append("outside")
        return render(ns,blocks,targets)
    out=e["output"];t=rat(e["weight"])
    i,j=(v[0] for v in e["before"]["best_responses"])
    branch={"UNCHANGED":0,"ROW":1,"COLUMN":2}[e["branch"]]
    args=f"R C p pNew q qNew {s} {r} {c} {t} {i} {j} {branch}"
    blocks.extend([f"def pNew : Fin {m} → ℚ := {nested(out['x'])}",
                   f"def qNew : Fin {n} → ℚ := {nested(out['y'])}",
                   f"theorem checked : checkKiteConversion {args} = true := by\n  decide +kernel"])
    targets.append("checked")
    if conclusions:
        blocks.append(f"""theorem actual : ∃ hp : Simplex pNew, ∃ hq : Simplex qNew,
    ApproxNash (fun i j => (R i j : ℝ)) (fun j i => (C j i : ℝ))
      (realRow pNew hp) (realRow qNew hq) ({s} : ℝ) :=
  checked_kite_conversion {args} checked""")
        targets.append("actual")
        exact_blocks(blocks,targets,out["evaluation"],m,n,"After","pNew","qNew")
    return render(ns,blocks,targets)


def emit_discounted(raw,receipt,*,conclusions=True,x1_source=False):
    check(raw,receipt)
    d=parse(raw)
    require(d["kind"]=="discounted","wrong discounted receipt kind")
    result=receipt["result"];n=d["n"];ns="ApproxDiscountedReplay"
    blocks=["import PermanssonResearch.ApplicationBridge.EquilibriumReceipt",
            "open PermanssonResearch.ApproxEquilibrium",
            "open PermanssonResearch.ApplicationBridge.EquilibriumReceipt",
            "open PermanssonResearch.ActionTrace PermanssonResearch.DiscountedVerification",
            "namespace "+ns,
            f"""def joint : JointDiscountedInput {n} where
  reward := {nested((d['R'],d['C']))}
  physical := {nested(d['P'])}
  policy := {nested((d['x'],d['y']))}
  discount := {nested(d['beta'])}
  value := {nested(d['V'])}
  physical_ok := by decide +kernel
  policy_ok := by decide +kernel
  discount_ok := by decide +kernel""",
            "def model0 := joint.first",
            "def model1 := joint.second"]
    targets=[]
    for i in range(2):
        R=max(abs(v) for m in (d["R"] if i==0 else d["C"]) for row in m for v in row)
        C=max(abs(v) for v in d["V"][i])
        eps,rho=rat(result["epsilon"][i]),rat(result["rho"][i])
        args=f"model{i} {eps} {rho} {rat(R)} {rat(C)}"
        blocks.append(f"theorem checked{i} : checkDiscounted {args} = true := by\n  decide +kernel")
        targets.append(f"checked{i}")
        if conclusions:
            qvals=tuple(ev["row_scores" if i==0 else "column_scores"] for ev in result["evaluations"])
            means=tuple(ev["payoff"][i] for ev in result["evaluations"])
            regrets=tuple(ev["regret"][i] for ev in result["evaluations"])
            residuals=tuple(abs(d["V"][i][s]-Q(means[s])) for s in range(n))
            cont=result["continuation"][i]
            if i==1:cont=tuple(transpose(m) for m in cont)
            widths=tuple(z["widths"][i] for z in result["normalized"])
            norms=tuple(z["regret"][i] for z in result["normalized"])
            blocks.extend([
                f"def qTable{i} : Fin {n} → Fin 2 → ℚ := {nested(qvals)}",
                f"def meanTable{i} : Fin {n} → ℚ := {nested(means)}",
                f"def regretTable{i} : Fin {n} → ℚ := {nested(regrets)}",
                f"def residualTable{i} : Fin {n} → ℚ := {nested(residuals)}",
                f"def contTable{i} : Fin {n} → Fin 2 → Fin 2 → ℚ := {nested(cont)}",
                f"def widthTable{i} : Fin {n} → ℚ := {nested(widths)}",
                f"def normTable{i} : Fin {n} → ℚ := {nested(norms)}",
                f"""theorem outputs{i} :
    (∀ s a b, model{i}.continuation s a b = contTable{i} s a b) ∧
    (∀ s a, model{i}.qval s a = qTable{i} s a) ∧
    (∀ s, model{i}.mean s = meanTable{i} s) ∧
    (∀ s, max (model{i}.qval s 0) (model{i}.qval s 1) - model{i}.mean s = regretTable{i} s) ∧
    (∀ s, |model{i}.value s - model{i}.mean s| = residualTable{i} s) ∧
    (∃ s, regretTable{i} s = {eps}) ∧ (∃ s, residualTable{i} s = {rho}) ∧
    (∀ s, widthTable{i} s =
      max (max (contTable{i} s 0 0) (contTable{i} s 0 1))
        (max (contTable{i} s 1 0) (contTable{i} s 1 1)) -
      min (min (contTable{i} s 0 0) (contTable{i} s 0 1))
        (min (contTable{i} s 1 0) (contTable{i} s 1 1))) ∧
    (∀ s, if widthTable{i} s = 0 then normTable{i} s = 0 ∧ regretTable{i} s = 0
          else normTable{i} s * widthTable{i} s = regretTable{i} s) := by
  decide +kernel""",
                f"""theorem actual{i} (σ : BehavioralPolicy (Fin {n}) (Fin 2)) (μ : Row (Fin {n})) :
    payoff model{i}.game σ μ - payoff model{i}.game model{i}.policy μ ≤
      (({eps}:ℝ)+2*({rho}:ℝ))/(1-model{i}.game.discount) :=
  checked_discounted {args} checked{i} σ μ"""])
            targets.extend((f"outputs{i}",f"actual{i}"))
    if x1_source:
        require(n==2 and conclusions,"X1 source replay requires the two-state profile")
        blocks.append("""theorem sourceTables :
    (∀ i s a b, joint.reward i s a b = x1Reduced.reward i s a b) ∧
    (∀ s a b z, joint.physical s a b z = x1Reduced.physical s a b z) ∧
    (∀ i s a, joint.policy i s a = x1Reduced.policy i s a) ∧
    (∀ i, joint.discount i = x1Reduced.discount i) ∧
    (∀ i s, joint.value i s = x1Reduced.value i s) := by
  decide +kernel""")
        targets.extend(("sourceTables",))
        blocks.append("#print axioms PermanssonResearch.ApplicationBridge.EquilibriumReceipt.x1_reduced_actual_Q_first\n#print axioms PermanssonResearch.ApplicationBridge.EquilibriumReceipt.x1_reduced_actual_Q_second")
    return render(ns,blocks,targets)


def emit_transport_fixture(raw,receipt):
    """Restrict original-model replay to the registered three-state benchmark.

    Arbitrary numeric transport inputs are NOT promoted by this function.
    """
    check(raw,receipt);d=parse(raw);e=receipt["result"]
    require(d["kind"]=="transport" and d["n"]==3 and d["horizon"]==3
            and d["region"]==(0,1) and d["comparison"]==(0,1)
            and d["intervention"]==(1,0),"unsupported original-model transport fixture")
    p=(Q(1),Q(0));pt=(Q(9,10),Q(1,10))
    require(d["x"]==d["y"]==d["y_tilde"]==(p,)*3 and d["x_tilde"]==(pt,)*3,
            "unsupported transport policy")
    require(all(d["P"][s][a][b][z]==Q(z==(2 if a or b else s))
                for s in range(3) for a in range(2) for b in range(2) for z in range(3)),
            "unsupported physical kernel")
    ns="ApproxTransportReplay"
    blocks=["import PermanssonResearch.Games.RegretRegimeCounterexample",
            "import PermanssonResearch.ApplicationBridge.EquilibriumReceipt",
            "open PermanssonLean PermanssonLean.RegimeSpecification PermanssonLean.ProbabilitySupport",
            "open PermanssonResearch.ApproxEquilibrium.Examples",
            "open PermanssonResearch.ApplicationBridge.EquilibriumReceipt (x1Bool)",
            "namespace "+ns,
            f"def P : Fin 3 → Fin 2 → Fin 2 → Fin 3 → ℚ := {nested(d['P'])}",
            f"def x : Fin 3 → Fin 2 → ℚ := {nested(d['x'])}",
            f"def y : Fin 3 → Fin 2 → ℚ := {nested(d['y'])}",
            f"def xt : Fin 3 → Fin 2 → ℚ := {nested(d['x_tilde'])}",
            f"def yt : Fin 3 → Fin 2 → ℚ := {nested(d['y_tilde'])}",
            f"def regionMask : Fin 3 → Bool := {mask(3,d['region'])}",
            f"def comparisonMask : Fin 3 → Bool := {mask(3,d['comparison'])}",
            f"def horizon : ℕ := {d['horizon']}",
            f"def replacementAction : Fin 2 × Fin 2 := ({d['intervention'][0]}, {d['intervention'][1]})",
            """def LiteralInputs : Prop :=
  (∀ s a b z, P s a b z = if z=nextWorld s (x1Bool a,x1Bool b) then 1 else 0) ∧
  (∀ s a, x s a = coinRow 0 (x1Bool a) ∧ y s a = coinRow 0 (x1Bool a) ∧
    xt s a = coinRow (1/10) (x1Bool a) ∧ yt s a = coinRow 0 (x1Bool a)) ∧
  (∀ s, regionMask s = decide (s≠2) ∧ comparisonMask s = decide (s≠2)) ∧
  horizon = 3 ∧ replacementAction = (1,0)

instance : Decidable LiteralInputs := by
  unfold LiteralInputs
  infer_instance

theorem literal_inputs : LiteralInputs := by
  decide +kernel""",
            f"""theorem actual_margin : LiteralInputs ∧
    constitutiveMargin (model 0 0 (by norm_num) (by norm_num)) specification
      (family 0 0 (by norm_num) (by norm_num)) survivalProperty
      (comparison 0 0 (by norm_num) (by norm_num)) (intervention 0 0 (by norm_num) (by norm_num)) =
        ({rat(e['finite_margin'])}:ℝ) ∧
    constitutiveMargin (model (1/10) 0 (by norm_num) (by norm_num)) specification
      (family (1/10) 0 (by norm_num) (by norm_num)) survivalProperty
      (comparison (1/10) 0 (by norm_num) (by norm_num))
      (intervention (1/10) 0 (by norm_num) (by norm_num)) =
        ({rat(e['approximate_finite_margin'])}:ℝ) := by
  refine ⟨literal_inputs, ?_⟩
  simpa using actual_sharp_margins""",
            f"""theorem actual_bound : LiteralInputs ∧
    |constitutiveMargin (model (1/10) 0 (by norm_num) (by norm_num)) specification
      (family (1/10) 0 (by norm_num) (by norm_num)) survivalProperty
      (comparison (1/10) 0 (by norm_num) (by norm_num))
      (intervention (1/10) 0 (by norm_num) (by norm_num)) -
      constitutiveMargin (model 0 0 (by norm_num) (by norm_num)) specification
      (family 0 0 (by norm_num) (by norm_num)) survivalProperty
      (comparison 0 0 (by norm_num) (by norm_num))
      (intervention 0 0 (by norm_num) (by norm_num))| ≤
      ({rat(e['baseline_path_budget'])}:ℝ)+({rat(e['intervention_path_budget'])}:ℝ) := by
  refine ⟨literal_inputs, ?_⟩
  have h := dominant_original_margin_transport (1/10) (by norm_num)
  have hbudget :
      geometricTVEnvelope
        (PermanssonResearch.ApproxEquilibrium.rationalGain
          dominant (coinRow (1/10)) (coinRow 0) false : ℝ) 3 =
      ({rat(e['baseline_path_budget'])}:ℝ)+({rat(e['intervention_path_budget'])}:ℝ) := by
    rw [(dominant_regret_attained (1/10)).1]
    norm_num [geometricTVEnvelope]
  rw [hbudget] at h
  exact h""",
            f"""theorem numeric_bound :
    |({rat(e['approximate_finite_margin'])}:ℝ)-({rat(e['finite_margin'])}:ℝ)| ≤
      ({rat(e['baseline_path_budget'])}:ℝ)+({rat(e['intervention_path_budget'])}:ℝ) := by
  have h := actual_bound.2
  rw [actual_margin.2.1, actual_margin.2.2] at h
  exact h""",
            "#print axioms PermanssonResearch.ApproxEquilibrium.Examples.original_margin_transport",
            "#print axioms PermanssonResearch.ApproxEquilibrium.Examples.transport_instance",
            "#print axioms PermanssonResearch.ApproxEquilibrium.Examples.dominant_regret_action_error",
            "#print axioms PermanssonResearch.ApproxEquilibrium.Examples.dominant_original_margin_transport",
            "#print axioms PermanssonResearch.ApproxEquilibrium.Examples.both_budgets_necessary",
            "#print axioms PermanssonResearch.ApproxEquilibrium.Examples.actual_survival",
            "#print axioms PermanssonResearch.ApproxEquilibrium.Examples.forever_zero_zero",
            "#print axioms PermanssonResearch.ApproxEquilibrium.Examples.forever_leak_zero",
            "#print axioms PermanssonResearch.ApproxEquilibrium.Examples.forever_coordination_exit",
            "#print axioms PermanssonResearch.ApproxEquilibrium.Examples.no_vanishing_regret_modulus",
            "#print axioms PermanssonResearch.ApproxEquilibrium.Examples.dominant_discounted_exact",
            "#print axioms PermanssonResearch.ApproxEquilibrium.Examples.trace_stateLaw_actual"]
    return render(ns,blocks,["literal_inputs","actual_margin","actual_bound","numeric_bound"])

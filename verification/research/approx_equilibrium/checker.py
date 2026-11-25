"""Independent exact receipt reconstruction. Imports no candidate producer."""
from fractions import Fraction as Q
from .contract import parse, pack, identity, RECEIPT, keys, require

def joint_value(R,x,y):
    return sum((x[i]*y[j]*R[i][j] for i in range(len(x)) for j in range(len(y))),Q(0))

def eval_profile(R,C,x,y):
    m,n=len(x),len(y)
    r=tuple(joint_value(R,tuple(Q(i==k) for i in range(m)),y) for k in range(m))
    c=tuple(joint_value(C,x,tuple(Q(j==k) for j in range(n))) for k in range(n))
    u,v=joint_value(R,x,y),joint_value(C,x,y)
    return {"row_scores":r,"column_scores":c,"payoff":(u,v),
            "regret":(max(z-u for z in r),max(z-v for z in c)),
            "best_responses":(tuple(i for i in range(m) if r[i]==max(r)),
                              tuple(j for j in range(n) if c[j]==max(c)))}

def projection(p,scores):
    best=max(scores)
    good=tuple(i for i,s in enumerate(scores) if s==best)
    diff=tuple(best-s for s in scores)
    mass=1-sum((p[i] for i in good),Q(0))
    q=list(p)
    for i in range(len(p)):
        if i not in good: q[i]=Q(0)
    q[good[0]]+=mass
    gap=min((v for v in diff if v>0),default=None)
    regret=sum((p[i]*diff[i] for i in range(len(p))),Q(0))
    distance=sum((abs(a-b) for a,b in zip(p,q)),Q(0))/2
    bound=min(Q(1),regret/gap) if gap is not None else Q(0)
    require(distance<=bound and distance==mass,"projection error")
    return {"best_responses":good,"nonbest_mass":mass,"gap":gap,"projection":q,"tv":distance,"bound":bound}

def static(d):
    e=eval_profile(d["R"],d["C"],d["x"],d["y"])
    if d["kind"]=="regret":
        return dict(e,epsilon=d["epsilon"],threshold_met=max(e["regret"])<=d["epsilon"],
            exact_nash=max(e["regret"])==0,fixed_opponent_projection=(
            projection(d["x"],e["row_scores"]),projection(d["y"],e["column_scores"])))
    s=d["epsilon"]; r,c=e["regret"]
    lhs=(r+s*(c-r),c+s*(r-c))
    inside=all(v<=s for v in lhs)
    o={"before":e,"threshold":s,"kite_lhs":lhs,"in_kite":inside}
    if not inside:
        return dict(o,branch="OUTSIDE_KITE",weight=None,output=None)
    x,y=list(d["x"]),list(d["y"]); t=Q(0); branch="UNCHANGED"
    if r>s:
        branch="ROW";t=(r-s)/r;x=[(1-t)*p for p in x];x[e["best_responses"][0][0]]+=t
    elif c>s:
        branch="COLUMN";t=(c-s)/c;y=[(1-t)*p for p in y];y[e["best_responses"][1][0]]+=t
    ev=eval_profile(d["R"],d["C"],x,y)
    require(max(ev["regret"])<=s,"kite output fails threshold")
    return dict(o,branch=branch,weight=t,output={"x":x,"y":y,"evaluation":ev})

def dynamic(d):
    n=d["n"]; matrices=[[],[]]; evs=[]; norm=[]
    for s in range(n):
        for i,stage in enumerate((d["R"],d["C"])):
            m=[]
            for a in range(2):
                rr=[]
                for b in range(2):
                    rr.append(sum((d["P"][s][a][b][z]*(stage[s][a][b]+d["beta"][i]*d["V"][i][z])
                                   for z in range(n)),Q(0)))
                m.append(rr)
            matrices[i].append(m)
        e=eval_profile(matrices[0][-1],matrices[1][-1],d["x"][s],d["y"][s]);evs.append(e)
        widths=[]
        for i in range(2):
            vals=[v for r in matrices[i][-1] for v in r]
            widths.append(max(vals)-min(vals))
        norm.append({"widths":widths,"regret":[e["regret"][i]/widths[i] if widths[i] else Q(0) for i in range(2)]})
    eps=[max(e["regret"][i] for e in evs) for i in range(2)]
    rho=[max(abs(d["V"][i][s]-evs[s]["payoff"][i]) for s in range(n)) for i in range(2)]
    return {"continuation":matrices,"evaluations":evs,"epsilon":eps,"rho":rho,"discount":d["beta"],
            "normalized":norm,"full_history_bound":[(eps[i]+2*rho[i])/(1-d["beta"][i]) for i in range(2)]}

def distance(p,q):
    return 1-sum((min(a,b) for a,b in zip(p,q)),Q(0))

def process(d):
    n=d["n"]; P=d["P"]; B=d["region"]; starts=d["comparison"]; T=d["horizon"]
    def rows(x,y):
        out=[]
        for s in range(n):
            r=[Q(0)]*n
            for a in range(2):
                for b in range(2):
                    for z,p in enumerate(P[s][a][b]):
                        r[z]+=x[s][a]*y[s][b]*p
            out.append(r)
        return out
    K=rows(d["x"],d["y"]);L=rows(d["x_tilde"],d["y_tilde"])
    a,b=d["intervention"];J=[P[s][a][b] for s in range(n)]
    ds=[(distance(d["x"][s],d["x_tilde"][s]),distance(d["y"][s],d["y_tilde"][s])) for s in range(n)]
    product=[u+v-u*v for u,v in ds];delta=max(product)
    obs=[distance(K[s],L[s]) for s in range(n)]
    require(all(a<=b for a,b in zip(obs,product)),"kernel error exceeds action bound")
    def forward(K):
        result=[]
        for s in range(n):
            p=[Q(z==s and s in B) for z in range(n)]
            for _ in range(T):
                p=[sum((p[i]*K[i][j] for i in B),Q(0)) if j in B else Q(0) for j in range(n)]
            result.append(sum(p,Q(0)))
        return result
    bv,lv,jv=(forward(M) for M in (K,L,J))
    e=1-(1-delta)**T
    require(all(abs(a-b)<=e for a,b in zip(bv,lv)),"path error exceeds bound")
    effect=[abs(bv[s]-jv[s]) for s in starts];alt=[abs(lv[s]-jv[s]) for s in starts]
    lower=max(Q(0),min(effect)-e)
    require(min(alt)>=lower,"margin transport inequality fails")
    return {"baseline_kernel":K,"approximate_kernel":L,"intervention_kernel":J,
            "player_tv":ds,"action_product_budget":product,"observed_kernel_tv":obs,
            "baseline_kernel_budget":delta,"intervention_kernel_budget":Q(0),
            "baseline_path_budget":e,"intervention_path_budget":Q(0),
            "horizon":T,"comparison":starts,"region":B,"baseline_survival":bv,
            "approximate_survival":lv,"intervention_survival":jv,"effects":effect,
            "approximate_effects":alt,"finite_margin":min(effect),
            "approximate_finite_margin":min(alt),"margin_lower_bound":lower,
            "typed_world_fixed":True,"update":"identity_on_unit_memory"}

def check(raw,receipt):
    d=parse(raw)
    keys(receipt,("format","input_sha256","kind","result"))
    require(receipt["format"]==RECEIPT and receipt["input_sha256"]==identity(raw)
            and receipt["kind"]==d["kind"],"foreign receipt")
    expected=static(d) if d["kind"] in ("regret","kite") else dynamic(d) if d["kind"]=="discounted" else process(d)
    # Canonical comparison, not Python's bool/int equality.
    from .contract import canonical
    require(canonical(receipt["result"])==canonical(pack(expected)),"incorrect or incomplete receipt")
    result=receipt["result"]
    if d["kind"]=="regret":
        disposition="THRESHOLD_MET" if result["threshold_met"] else "THRESHOLD_NOT_MET"
    elif d["kind"]=="kite":
        disposition="CONVERTED_OR_RETAINED" if result["in_kite"] else "OUTSIDE_KITE"
    else:
        disposition="BOUNDS_RECONSTRUCTED"
    return {"numeric_status":"VERIFIED_EXACT_RATIONAL","disposition":disposition,
            "lean_status":"NOT_EXECUTED","original_regime_certificate":False,
            "empirical_identification":"NOT_IDENTIFIED"}

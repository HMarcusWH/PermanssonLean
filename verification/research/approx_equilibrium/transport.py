"""Same-P, identity-U finite product policy comparison.

The output is a numeric finite survival/constitutive-effect comparison, not
a proof that an arbitrary external model inhabits the original regime API.
"""
from fractions import Fraction as Q

def tv(p,q):
    return sum((abs(a-b) for a,b in zip(p,q)),Q(0))/2

def kernel(P,x,y):
    n=len(P)
    return tuple(tuple(sum((x[s][a]*y[s][b]*P[s][a][b][z]
                for a in range(2) for b in range(2)),Q(0)) for z in range(n)) for s in range(n))

def survival(K,B,T):
    v=tuple(Q(i in B) for i in range(len(K)))
    for _ in range(T):
        v=tuple(sum((p*z for p,z in zip(K[i],v)),Q(0)) if i in B else Q(0)
                for i in range(len(K)))
    return v

def produce(d):
    P,x,y,xt,yt=(d[k] for k in ("P","x","y","x_tilde","y_tilde"))
    n=d["n"]; T=d["horizon"]; B=d["region"]; starts=d["comparison"]
    a,b=d["intervention"]
    K=kernel(P,x,y); L=kernel(P,xt,yt)
    J=tuple(P[s][a][b] for s in range(n))
    ds=tuple((tv(x[s],xt[s]),tv(y[s],yt[s])) for s in range(n))
    product=tuple(1-(1-u)*(1-v) for u,v in ds)
    delta=max(product)
    observed=tuple(tv(K[s],L[s]) for s in range(n))
    e=1-(1-delta)**T
    bv=survival(K,B,T); lv=survival(L,B,T); jv=survival(J,B,T)
    effects=tuple(abs(bv[s]-jv[s]) for s in starts)
    alt=tuple(abs(lv[s]-jv[s]) for s in starts)
    return {"baseline_kernel":K,"approximate_kernel":L,"intervention_kernel":J,
            "player_tv":ds,"action_product_budget":product,"observed_kernel_tv":observed,
            "baseline_kernel_budget":delta,"intervention_kernel_budget":Q(0),
            "baseline_path_budget":e,"intervention_path_budget":Q(0),
            "horizon":T,"comparison":starts,"region":B,
            "baseline_survival":bv,"approximate_survival":lv,"intervention_survival":jv,
            "effects":effects,"approximate_effects":alt,"finite_margin":min(effects),
            "approximate_finite_margin":min(alt),"margin_lower_bound":max(Q(0),min(effects)-e),
            "typed_world_fixed":True,"update":"identity_on_unit_memory"}

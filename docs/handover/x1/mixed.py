exec(open('search.py').read().split('print("--- symmetric mixed search")')[0])
for p in (F(1,2), F(1,3), F(2,3)):
    for v1 in (F(1,2), F(2,5), F(3,5)):
        th2 = dict(th); th2['v0'] = F(0); th2['v1'] = v1
        pol = ((F(0), p), (F(0), p))
        chi = solve_param_for_mixed(th2, pol, 'chi', 0, 1)
        if chi < 0: continue
        th2['chi'] = chi
        ok, V = is_mpe(th2, pol)
        V2 = values(th2, pol)
        gap0 = Q(th2, 0, V2, pol, 0, 1) - Q(th2, 0, V2, pol, 0, 0)
        print(f"p={p} v1={v1} chi={chi} MPE={ok} V={V2[0]} gap(x0)={gap0}")

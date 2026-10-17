from fractions import Fraction as F
from itertools import product

def p_rep(th, x, a):
    r = th['r1'] if x == 1 else th['r0']
    return min(F(1), max(F(0), r - th['d'] * (a[0] + a[1])))

def reward(th, i, x, a):
    ai, aj = a[i], a[1 - i]
    v = th['v1'] if x == 1 else th['v0']
    return v * ai - th['chi'] * ai * aj - th['lam'] * (1 - x)

def solve2(A, b):
    (a11, a12), (a21, a22) = A
    det = a11 * a22 - a12 * a21
    return ((b[0] * a22 - a12 * b[1]) / det, (a11 * b[1] - a21 * b[0]) / det)

def values(th, pol):
    """pol[i][x] = prob of a_i = 1 at x (mixed). Returns V_i(x) for i=0,1."""
    V = []
    for i in range(2):
        beta = th['beta'][i]
        A = [[F(0), F(0)], [F(0), F(0)]]; b = [F(0), F(0)]
        for x in (0, 1):
            A[x][x] += 1
            for a in product((0, 1), repeat=2):
                pa = (pol[0][x] if a[0] else 1 - pol[0][x]) * (pol[1][x] if a[1] else 1 - pol[1][x])
                if pa == 0: continue
                b[x] += pa * reward(th, i, x, a)
                q = p_rep(th, x, a)
                A[x][1] -= pa * beta * q
                A[x][0] -= pa * beta * (1 - q)
        V.append(solve2(A, b))
    return V

def Q(th, i, V, pol, x, ai):
    beta = th['beta'][i]; tot = F(0)
    for aj in (0, 1):
        pj = pol[1 - i][x] if aj else 1 - pol[1 - i][x]
        if pj == 0: continue
        a = (ai, aj) if i == 0 else (aj, ai)
        q = p_rep(th, x, a)
        tot += pj * (reward(th, i, x, a) + beta * (q * V[i][1] + (1 - q) * V[i][0]))
    return tot

def is_mpe(th, pol):
    V = values(th, pol)
    for i in range(2):
        for x in (0, 1):
            q0, q1 = Q(th, i, V, pol, x, 0), Q(th, i, V, pol, x, 1)
            if max(q0, q1) > V[i][x]: return False, V
            p = pol[i][x]
            if p > 0 and q1 != V[i][x]: return False, V
            if p < 1 and q0 != V[i][x]: return False, V
    return True, V

th = dict(r0=F(1,4), r1=F(9,10), d=F(1,4), beta=(F(9,10), F(9,10)), v0=F(1,5), v1=F(1,2), chi=F(3,5), lam=F(1,10))
found = []
for p0 in product((F(0), F(1)), repeat=2):
    for p1 in product((F(0), F(1)), repeat=2):
        pol = (p0, p1)
        ok, V = is_mpe(th, pol)
        if ok: found.append((pol, V))
for f in found: print("pure MPE", f)

def indiff_gap(th, pol, i, x):
    V = values(th, pol)
    return Q(th, i, V, pol, x, 1) - Q(th, i, V, pol, x, 0)

def solve_param_for_mixed(th, pol, key, i, x):
    """Indifference gap is affine in reward parameter `key`; solve exactly."""
    t0, t1 = dict(th), dict(th)
    t0[key], t1[key] = F(0), F(1)
    g0, g1 = indiff_gap(t0, pol, i, x), indiff_gap(t1, pol, i, x)
    return -g0 / (g1 - g0)

print("--- symmetric mixed search")
for p in (F(1,2), F(1,3), F(2,3), F(1,4)):
    for chi in (F(1,5), F(2,5), F(3,5), F(4,5)):
        th2 = dict(th); th2['chi'] = chi
        pol = ((F(0), p), (F(0), p))
        v1 = solve_param_for_mixed(th2, pol, 'v1', 0, 1)
        if v1 < 0: continue
        th2['v1'] = v1
        ok, V = is_mpe(th2, pol)
        if ok:
            print("p=",p,"chi=",chi,"v1=",v1,"V=",V)

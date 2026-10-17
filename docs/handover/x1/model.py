from fractions import Fraction as F
from itertools import product

TH = dict(r0=F(1,4), r1=F(9,10), d=F(1,4), beta=(F(9,10), F(9,10)), v0=F(0), v1=F(1,2),
          chi=F(193,211), lam=F(1,10))
PI = {0: F(0), 1: F(1,2)}           # MPE extraction prob by world state
M = 2
EPS = F(1,10)
B_REF = {0: F(-1,20), 1: F(1,20)}   # learner reference payoffs b_i(x)

def p_rep(x, a):
    r = TH['r1'] if x == 1 else TH['r0']
    return min(F(1), max(F(0), r - TH['d'] * (a[0] + a[1])))

def reward(i, x, a):
    ai, aj = a[i], a[1 - i]
    v = TH['v1'] if x == 1 else TH['v0']
    return v * ai - TH['chi'] * ai * aj - TH['lam'] * (1 - x)

def sgn(z): return (z > 0) - (z < 0)
def clip(v): return max(0, min(M, v))

STATES = [((q1, q2), x) for q1 in range(M + 1) for q2 in range(M + 1) for x in (0, 1)]

def alpha_E(y):
    (q, x) = y
    p = PI[x]
    return {a: (p if a[0] else 1 - p) * (p if a[1] else 1 - p) for a in product((0, 1), repeat=2)}

def alpha_L(y):
    (q, x) = y
    pr = [(1 - EPS) * F(q[i], M) + EPS / 2 for i in range(2)]
    return {a: (pr[0] if a[0] else 1 - pr[0]) * (pr[1] if a[1] else 1 - pr[1]) for a in product((0, 1), repeat=2)}

def U_E(y, a, x2):
    return {y[0]: F(1)}

def U_L(y, a, x2):
    (q, x) = y
    q2 = tuple(clip(q[i] + (2 * a[i] - 1) * sgn(reward(i, x, a) - B_REF[x])) for i in range(2))
    return {q2: F(1)}

def kernel(alpha, U):
    K = {}
    for y in STATES:
        row = {}
        for a, pa in alpha(y).items():
            if pa == 0: continue
            q = p_rep(y[1], a)
            for x2, px in ((1, q), (0, 1 - q)):
                if px == 0: continue
                for s2, ps in U(y, a, x2).items():
                    z = (s2, x2)
                    row[z] = row.get(z, F(0)) + pa * px * ps
        assert sum(row.values()) == 1
        K[y] = row
    return K

KE, KL = kernel(alpha_E, U_E), kernel(alpha_L, U_L)

def reachable(K, y):
    seen, stack = {y}, [y]
    while stack:
        u = stack.pop()
        for z in K[u]:
            if z not in seen: seen.add(z); stack.append(z)
    return seen

def stationary(K, states):
    idx = {s: i for i, s in enumerate(states)}; n = len(states)
    A = [[F(0)] * n for _ in range(n)]
    for s in states:
        for z, p in K[s].items():
            if z in idx: A[idx[z]][idx[s]] += p
    for i in range(n): A[i][i] -= 1
    A[-1] = [F(1)] * n; b = [F(0)] * (n - 1) + [F(1)]
    for c in range(n):
        piv = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[piv] = A[piv], A[c]; b[c], b[piv] = b[piv], b[c]
        for r in range(n):
            if r != c and A[r][c] != 0:
                m = A[r][c] / A[c][c]
                A[r] = [u - m * v for u, v in zip(A[r], A[c])]; b[r] -= m * b[c]
    return {s: b[idx[s]] / A[idx[s]][idx[s]] for s in states}

y0 = ((1, 1), 1)
RE, RL = reachable(KE, y0), reachable(KL, y0)
print("E reachable", len(RE), "L reachable", len(RL))
piE = stationary(KE, sorted(RE)); piL = stationary(KL, sorted(RL))
occE = sum(p for s, p in piE.items() if s[1] == 1); occL = sum(p for s, p in piL.items() if s[1] == 1)
print("E long-run replete occupation", occE, float(occE)); print("L long-run replete occupation", occL, float(occL))
# killed persistence of B = S x {1}
def killed_persist(K, y, L):
    v = {s: F(1) if s[1] == 1 else F(0) for s in STATES}
    for _ in range(L):
        v = {s: (sum(p * v[z] for z, p in K[s].items() if z[1] == 1) if s[1] == 1 else F(0)) for s in STATES}
    return v[y]
for L in (1, 5, 20):
    print("L=",L,"persist E", float(killed_persist(KE, y0, L)), "persist L", float(killed_persist(KL, y0, L)))

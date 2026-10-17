"""Exact-Fraction adversaries for F1 (multi-agent closed-loop vs opponent-locked).

Independent executable cross-checks of PermanssonResearch/MultiAgent/*. Finite
two-player conditional-product games only; these are NOT proofs of the general
measurable-space Lean theorems. Covers the spec section 6 test list: response vs
frozen (MA1), baseline-agreeing anchors that differ off support (MA2), correlated
actions outside the product subclass (MA3), infeasible anchors, interventions
that change P, nonstationary anchors needing a clock, and direction vs uniform gap.
"""
from fractions import Fraction as F
from itertools import product
import random
import unittest

ZERO, ONE, HALF = F(0), F(1), F(1, 2)


def dirac(v):
    return {v: ONE}


def prod(mu, nu):
    out = {}
    for a, p in mu.items():
        for b, q in nu.items():
            out[(a, b)] = out.get((a, b), ZERO) + p * q
    return out


class Game:
    """Joint state y = ((s0, (s1, s2)), x); action a = (a1, a2).

    act1(y), act2(y): action laws; up0/up1/up2(y, a, x'): update laws;
    world(y, a): law of x'.  The induced one-step kernel is the frozen
    composition  α → P → U  with α = α₁ ⊗ α₂ and U = U₀ ⊗ (U₁ ⊗ U₂)."""

    def __init__(self, act1, act2, up0, up1, up2, world, joint_action=None):
        self.act1, self.act2 = act1, act2
        self.up0, self.up1, self.up2 = up0, up1, up2
        self.world = world
        self.joint_action = joint_action      # overrides α₁ ⊗ α₂ (correlated)

    def action(self, y):
        if self.joint_action is not None:
            return self.joint_action(y)
        return prod(self.act1(y), self.act2(y))

    def step(self, y):
        out = {}
        for a, pa in self.action(y).items():
            for x2, px in self.world(y, a).items():
                ups = prod(self.up0(y, a, x2), prod(self.up1(y, a, x2), self.up2(y, a, x2)))
                for s2, ps in ups.items():
                    z = (s2, x2)
                    out[z] = out.get(z, ZERO) + pa * px * ps
        return out

    def with_(self, **kw):
        d = dict(act1=self.act1, act2=self.act2, up0=self.up0, up1=self.up1,
                 up2=self.up2, world=self.world, joint_action=self.joint_action)
        d.update(kw)
        return Game(**d)


def prefix_law(G, y, T):
    law = {(y,): ONE}
    for _ in range(T):
        nxt = {}
        for w, p in law.items():
            for z, q in G.step(w[-1]).items():
                nxt[w + (z,)] = nxt.get(w + (z,), ZERO) + p * q
        law = nxt
    return law


def event_prob(law, pred):
    return sum((p for w, p in law.items() if pred(w)), ZERO)


def s1(y): return y[0][1][0]
def s2(y): return y[0][1][1]
def xw(y): return y[1]


def closed_loop(G, r1):
    """Replace player 1 (action + private update) only."""
    act, up = r1
    return G.with_(act1=act, up1=up)


def open_loop(G, r1, anchor):
    """Replace player 1 AND install a declared opponent anchor."""
    act, up = r1
    a_act, a_up = anchor
    return G.with_(act1=act, up1=up, act2=a_act, up2=a_up)


# --- the Boolean witness mirrored from ProtocolWitnesses.lean --------------------
BASE = Game(act1=lambda y: dirac(s1(y)),
            act2=lambda y: dirac(s1(y)),                 # reactive: copy player 1
            up0=lambda y, a, x: dirac(()),
            up1=lambda y, a, x: dirac(a[0]),
            up2=lambda y, a, x: dirac(a[1]),
            world=lambda y, a: dirac(a[0]))
R1 = (lambda y: dirac(True), lambda y, a, x: dirac(a[0]))
ANCHOR_CONST = (lambda y: dirac(False), lambda y, a, x: dirac(a[1]))
ANCHOR_WORLD = (lambda y: dirac(xw(y)), lambda y, a, x: dirac(a[1]))
Y0 = (((), (False, False)), False)
T = 2


def psi(G, y=Y0, horizon=T):
    """Opponent's recorded action at time `horizon` is 'extract' (True)."""
    return event_prob(prefix_law(G, y, horizon), lambda w: s2(w[horizon]))


class ResponseVersusFrozenTests(unittest.TestCase):

    def test_ma1_closed_loop_differs_from_opponent_locked(self):
        z0, zcl, zol = psi(BASE), psi(closed_loop(BASE, R1)), psi(open_loop(BASE, R1, ANCHOR_CONST))
        self.assertEqual((z0, zcl, zol), (ZERO, ONE, ZERO))
        d_cl, d_ol, gap = abs(zcl - z0), abs(zol - z0), abs(zcl - zol)
        self.assertEqual((d_cl, d_ol, gap), (ONE, ZERO, ONE))
        self.assertEqual(gap, d_cl)                          # Δ_OL = 0 ⇒ A = Δ_CL

    def test_agreement_with_world_reading_anchor(self):
        self.assertEqual(psi(closed_loop(BASE, R1)), psi(open_loop(BASE, R1, ANCHOR_WORLD)))

    def test_difference_needs_an_intervention_reachable_state(self):
        """At horizon 1 the opponent has not yet seen the counterfactual: the
        protocols agree; they separate only after the reachable state x = True."""
        self.assertEqual(psi(closed_loop(BASE, R1), horizon=1),
                         psi(open_loop(BASE, R1, ANCHOR_CONST), horizon=1))
        self.assertNotEqual(psi(closed_loop(BASE, R1), horizon=2),
                            psi(open_loop(BASE, R1, ANCHOR_CONST), horizon=2))


class AnchorIdentificationTests(unittest.TestCase):

    def test_ma2_baseline_agreeing_anchors_differ_off_support(self):
        support = {z for w in prefix_law(BASE, Y0, 6) for z in w}
        self.assertEqual(support, {Y0})
        for y in support:
            self.assertEqual(ANCHOR_CONST[0](y), ANCHOR_WORLD[0](y))
        off = (((), (True, False)), True)                    # reachable only under J
        self.assertNotIn(off, support)
        self.assertNotEqual(ANCHOR_CONST[0](off), ANCHOR_WORLD[0](off))
        self.assertNotEqual(psi(open_loop(BASE, R1, ANCHOR_CONST)),
                            psi(open_loop(BASE, R1, ANCHOR_WORLD)))


class ProductSubclassTests(unittest.TestCase):

    CORR = {(True, True): HALF, (False, False): HALF}

    def test_ma3_correlated_law_not_product(self):
        m1 = {b: sum((p for (a1, _), p in self.CORR.items() if a1 == b), ZERO) for b in (True, False)}
        m2 = {b: sum((p for (_, a2), p in self.CORR.items() if a2 == b), ZERO) for b in (True, False)}
        self.assertNotEqual(prod(m1, m2), {**self.CORR, (True, False): ZERO, (False, True): ZERO})
        # no product law at all: p1 q1 = 1/2, p0 q0 = 1/2, p1 q0 = 0 is infeasible
        for p1 in [F(k, 20) for k in range(21)]:
            for q1 in [F(k, 20) for k in range(21)]:
                law = prod({True: p1, False: 1 - p1}, {True: q1, False: 1 - q1})
                self.assertNotEqual({k: v for k, v in law.items() if v}, self.CORR)

    def test_ma3_product_misrepresents_coordination(self):
        """Forcing the correlated model into product form changes the property
        (probability of coordination): the subclass must be declared."""
        corr = BASE.with_(joint_action=lambda y: self.CORR, world=lambda y, a: dirac(a[0]))
        indep = BASE.with_(act1=lambda y: {True: HALF, False: HALF},
                           act2=lambda y: {True: HALF, False: HALF},
                           world=lambda y, a: dirac(a[0]))
        coord = lambda G: event_prob(prefix_law(G, Y0, 1), lambda w: s1(w[1]) == s2(w[1]))
        self.assertEqual((coord(corr), coord(indep)), (ONE, HALF))


class FeasibilityAndWorldTests(unittest.TestCase):

    def test_infeasible_anchor_rejected(self):
        """Feasible opponent actions depend on the state (cannot extract when
        the resource is depleted, x = True). An anchor putting mass on an
        infeasible action is not admissible; the declared menu must be checked."""
        feasible = lambda y: {False} if xw(y) else {True, False}
        always_extract = (lambda y: dirac(True), lambda y, a, x: dirac(a[1]))
        menu = [ANCHOR_CONST, ANCHOR_WORLD, always_extract]
        states = [((( ), (b1, b2)), x) for b1, b2, x in product((True, False), repeat=3)]

        def admissible(anchor):
            return all(set(anchor[0](y)) <= feasible(y) for y in states)

        self.assertEqual([admissible(a) for a in menu], [True, False, False])

    def test_intervention_changing_world_is_not_a_protocol(self):
        """A 'protocol' that also edits P changes the property even with the
        same strategic replacement: the protocol family must hold P fixed (Lean:
        protocol_world_eq)."""
        P_alt = lambda y, a: dirac(False)
        ol = open_loop(BASE, R1, ANCHOR_WORLD)
        ol_bad = ol.with_(world=P_alt)
        self.assertEqual((psi(ol), psi(ol_bad)), (ONE, ZERO))
        for y in [Y0, (((), (True, True)), True)]:
            for a in product((True, False), repeat=2):
                self.assertEqual(ol.world(y, a), BASE.world(y, a))
        self.assertNotEqual(ol_bad.world(Y0, (True, True)), BASE.world(Y0, (True, True)))


class ClockTests(unittest.TestCase):

    def test_nonstationary_anchor_needs_clock_state(self):
        """Anchor: 'false at t < 2, true afterwards'. Under the frozen OL run the
        joint state at t = 1 and t = 2 coincides, so no stationary kernel on the
        UNAUGMENTED state reproduces it; with a clock in S0 it is stationary."""
        G = open_loop(BASE, (lambda y: dirac(False), lambda y, a, x: dirac(a[0])), ANCHOR_CONST)
        orbit = [w for w in prefix_law(G, Y0, 3)][0]
        self.assertEqual(orbit[1], orbit[2])                 # same state, t = 1, 2
        wanted = {1: False, 2: True}                          # required actions differ
        self.assertNotEqual(wanted[1], wanted[2])
        # clock-augmented common coordinate s0 = min(t, 2)
        clocked = G.with_(act2=lambda y: dirac(y[0][0] >= 2),
                          up0=lambda y, a, x: dirac(min(y[0][0] + 1, 2)))
        y0c = ((0, (False, False)), False)
        path = list(prefix_law(clocked, y0c, 3))[0]
        self.assertEqual([s2(z) for z in path], [False, False, False, True])


class DirectionVersusGapTests(unittest.TestCase):

    def test_v20_29_bounds_on_random_games(self):
        rng = random.Random(20261017)
        B = (True, False)

        def rlaw():
            p = F(rng.randint(0, 8), 8)
            return {True: p, False: 1 - p}

        for _ in range(60):
            tbl = {k: rlaw() for k in product(B, repeat=3)}
            tbl2 = {k: rlaw() for k in product(B, repeat=3)}
            G = Game(act1=lambda y, t=tbl: t[(s1(y), s2(y), xw(y))],
                     act2=lambda y, t=tbl2: t[(s1(y), s2(y), xw(y))],
                     up0=lambda y, a, x: dirac(()),
                     up1=lambda y, a, x: dirac(a[0]), up2=lambda y, a, x: dirac(a[1]),
                     world=lambda y, a: dirac(a[0] and not a[1]))
            r = (lambda y, p=rlaw(): p, lambda y, a, x: dirac(a[0]))
            anc = (lambda y, p=rlaw(): p, lambda y, a, x: dirac(a[1]))
            for y in [(((), (b1, b2)), x) for b1, b2, x in product(B, repeat=3)]:
                z0 = psi(G, y, 3)
                zc, zo = psi(closed_loop(G, r), y, 3), psi(open_loop(G, r, anc), y, 3)
                dc, do, gap = abs(zc - z0), abs(zo - z0), abs(zc - zo)
                self.assertLessEqual(abs(dc - do), gap)
                self.assertLessEqual(gap, dc + do)

    def test_direction_not_determined_by_gap(self):
        """Same protocol pair: Δ_CL > Δ_OL at one state, Δ_CL < Δ_OL at another,
        while the uniform gap bounds the margin difference (Lean:
        abs_constitutiveMargin_sub_le_of_protocolGap). Sign claims need their
        own hypotheses."""
        G = BASE
        cl = closed_loop(G, R1)
        anchors = [ANCHOR_CONST, ANCHOR_WORLD,
                   (lambda y: dirac(not xw(y)), lambda y, a, x: dirac(a[1]))]
        states = [(((), (b1, b2)), x) for b1, b2, x in product((True, False), repeat=3)]
        signs = set()
        for anc in anchors:
            ol = open_loop(G, R1, anc)
            gaps, dcs, dos = [], [], []
            for y in states:
                z0, zc, zo = psi(G, y), psi(cl, y), psi(ol, y)
                dcs.append(abs(zc - z0)); dos.append(abs(zo - z0)); gaps.append(abs(zc - zo))
                if dcs[-1] != dos[-1]:
                    signs.add(dcs[-1] > dos[-1])
            self.assertLessEqual(abs(min(dcs) - min(dos)), max(gaps))
        self.assertEqual(signs, {True, False})


if __name__ == "__main__":
    unittest.main()

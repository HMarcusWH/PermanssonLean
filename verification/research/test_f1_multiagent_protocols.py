"""Exact-Fraction adversaries for F1 (multi-agent closed-loop vs opponent-locked).

Independent executable cross-checks of PermanssonResearch/MultiAgent/*. Finite
two-player conditional-product games only; these are NOT proofs of the general
measurable-space Lean theorems. Covers the spec section 6 test list: response vs
frozen (MA1), a broader state-feedback counterexample (NOT strict MA2), the
scoped strict MA2 obstruction and endogenous-common-state loophole, correlated
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
ANCHOR_CONST = (lambda y: dirac(False), lambda y, a, x: dirac(a[1]))      # strict
ANCHOR_EXTRACT = (lambda y: dirac(True), lambda y, a, x: dirac(a[1]))     # strict
ANCHOR_WORLD = (lambda y: dirac(xw(y)), lambda y, a, x: dirac(a[1]))      # state feedback
Y0 = (((), (False, False)), False)
T = 2


def psi(G, y=Y0, horizon=T):
    """The opponent's action taken at time `horizon - 1` (recorded in s2 at time
    `horizon`) is 'extract' (True)."""
    return event_prob(prefix_law(G, y, horizon), lambda w: s2(w[horizon]))


B = (True, False)
ACTIONS = list(product(B, B))
STATES = [((), (b1, b2)) for b1, b2 in product(B, B)]
STATES = [(s, x) for s in STATES for x in B]


def anchor_key(y):
    return (y[0][0], s2(y))


def norm(law):
    """Laws as measures: drop explicit zero atoms before comparing."""
    return {k: v for k, v in law.items() if v != 0}


def strictly_non_reactive(anchor, states=STATES):
    """Lean IsStrictlyNonReactive: the action law depends only on (s0, s2), the
    update law only on ((s0, s2), a2)."""
    act, up = anchor
    for y, z in product(states, repeat=2):
        if anchor_key(y) == anchor_key(z) and norm(act(y)) != norm(act(z)):
            return False
    inputs = [(y, a, x) for y in states for a in ACTIONS for x in B]
    for (y, a, x), (z, b, w) in product(inputs, repeat=2):
        if (anchor_key(y) == anchor_key(z) and a[1] == b[1]
                and norm(up(y, a, x)) != norm(up(z, b, w))):
            return False
    return True


def exogenous_common(G, states=STATES):
    """Lean IsExogenousCommon: U0 factors through the old s0 alone."""
    inputs = [(y, a, x) for y in states for a in ACTIONS for x in B]
    by_s0 = {}
    for y, a, x in inputs:
        law = norm(G.up0(y, a, x))
        if y[0][0] in by_s0 and by_s0[y[0][0]] != law:
            return False
        by_s0[y[0][0]] = law
    return True


def is_protocol(Gi, G, r1, menu, states=STATES):
    """Lean protocol_admissible_cases: P and U0 are G's, player 1 is r1, and the
    opponent is G's own (CL) or a declared menu anchor (OL)."""
    ya = [(y, a) for y in states for a in ACTIONS]
    yax = [(y, a, x) for y, a in ya for x in B]
    same = lambda f, g, args: all(norm(f(*t)) == norm(g(*t)) for t in args)
    if Gi.joint_action is not None:          # correlated override: not a product game
        return False
    if not (same(Gi.world, G.world, ya) and same(Gi.up0, G.up0, yax)):
        return False
    if not (same(Gi.act1, r1[0], [(y,) for y in states]) and same(Gi.up1, r1[1], yax)):
        return False
    return any(same(Gi.act2, o[0], [(y,) for y in states]) and same(Gi.up2, o[1], yax)
               for o in [(G.act2, G.up2)] + list(menu))


def single_path(G, y, horizon):
    law = prefix_law(G, y, horizon)
    assert len(law) == 1 and sum(law.values(), ZERO) == ONE
    return next(iter(law))


def reachable(G, y, horizon):
    return {z for w in prefix_law(G, y, horizon) for z in w}


class ResponseVersusFrozenTests(unittest.TestCase):

    def test_strictness_classification(self):
        """Mirrors anchorConst_strict, anchorExtract_strict, anchorWorld_not_strict,
        baselineOpponent_not_strict."""
        self.assertTrue(strictly_non_reactive(ANCHOR_CONST))
        self.assertTrue(strictly_non_reactive(ANCHOR_EXTRACT))
        self.assertFalse(strictly_non_reactive(ANCHOR_WORLD))
        self.assertFalse(strictly_non_reactive((BASE.act2, BASE.up2)))
        # the UPDATE half of the predicate: constant action, update reading a1 or x'
        self.assertFalse(strictly_non_reactive((ANCHOR_CONST[0], lambda y, a, x: dirac(a[0]))))
        self.assertFalse(strictly_non_reactive((ANCHOR_CONST[0], lambda y, a, x: dirac(x))))
        # explicit zero atoms do not change the law
        self.assertTrue(strictly_non_reactive(
            (lambda y: {False: ONE, True: ZERO} if s1(y) else {False: ONE}, ANCHOR_CONST[1])))

    def test_ma1_closed_loop_differs_from_strict_opponent_locked(self):
        z0, zcl, zol = psi(BASE), psi(closed_loop(BASE, R1)), psi(open_loop(BASE, R1, ANCHOR_CONST))
        self.assertEqual((z0, zcl, zol), (ZERO, ONE, ZERO))
        d_cl, d_ol, gap = abs(zcl - z0), abs(zol - z0), abs(zcl - zol)
        self.assertEqual((d_cl, d_ol, gap), (ONE, ZERO, ONE))
        self.assertEqual(gap, d_cl)                          # Δ_OL = 0 ⇒ A = Δ_CL

    def test_ma1_locus(self):
        """Mirrors protocols_separate_after_reachable_state: same opponent law at
        Y0, different at the CL state at t = 1, which is off the baseline orbit;
        the property values coincide at horizon 1 and separate at horizon 2."""
        cl = closed_loop(BASE, R1)
        y1 = single_path(cl, Y0, 1)[1]
        self.assertEqual(y1, (((), (True, False)), True))
        self.assertNotIn(y1, reachable(BASE, Y0, 6))
        self.assertEqual(cl.act2(Y0), ANCHOR_CONST[0](Y0))
        self.assertNotEqual(cl.act2(y1), ANCHOR_CONST[0](y1))
        ol = open_loop(BASE, R1, ANCHOR_CONST)
        self.assertEqual(psi(cl, horizon=1), psi(ol, horizon=1))
        self.assertNotEqual(psi(cl, horizon=2), psi(ol, horizon=2))

    def test_agreement_with_strict_anchor(self):
        """Mirrors closedLoop_eq_openLoopExtract (strict) and
        closedLoop_eq_openLoopWorld (state feedback)."""
        self.assertEqual(psi(closed_loop(BASE, R1)), psi(open_loop(BASE, R1, ANCHOR_EXTRACT)))
        self.assertEqual(psi(closed_loop(BASE, R1)), psi(open_loop(BASE, R1, ANCHOR_WORLD)))


class AnchorIdentificationTests(unittest.TestCase):

    def test_declared_state_feedback_anchors_differ_off_support_not_strict_ma2(self):
        """Mirrors declared_anchors_agree_on_support_but_openLoop_differs.
        Explicitly rejects promotion of the world-reading anchor to strict MA2."""
        self.assertTrue(strictly_non_reactive(ANCHOR_CONST))
        self.assertFalse(strictly_non_reactive(ANCHOR_WORLD))
        support = reachable(BASE, Y0, 6)
        self.assertEqual(support, {Y0})
        for anc in (ANCHOR_CONST, ANCHOR_WORLD):
            for y in support:
                self.assertEqual(anc[0](y), BASE.act2(y))     # agrees with the BASELINE
                for a in ACTIONS:
                    for x in B:
                        self.assertEqual(anc[1](y, a, x), BASE.up2(y, a, x))
        off = (((), (True, False)), True)
        self.assertIn(off, reachable(closed_loop(BASE, R1), Y0, 2))   # reachable under CL
        for anc in (ANCHOR_CONST, ANCHOR_WORLD):                      # ...and under each OL run
            self.assertIn(off, reachable(open_loop(BASE, R1, anc), Y0, 2))
        self.assertNotIn(off, support)
        self.assertNotEqual(ANCHOR_CONST[0](off), ANCHOR_WORLD[0](off))
        self.assertNotEqual(psi(open_loop(BASE, R1, ANCHOR_CONST)),
                            psi(open_loop(BASE, R1, ANCHOR_WORLD)))

    def test_strict_recording_anchors_full_laws_equal_exhaustively(self):
        """Mirrors strict_recording_anchors_pathLaw_eq: ALL 256 deterministic
        treated action functions, ALL strict Bool-own-state action functions
        agreeing with baseline, own-action recording and exogenous Unit S0.
        Checks entire finite path laws rather than one coincident observable."""
        self.assertTrue(exogenous_common(BASE))
        anchors = []
        for at_false, at_true in product(B, repeat=2):
            table = {False: at_false, True: at_true}
            anc = (lambda y, table=table: dirac(table[s2(y)]), ANCHOR_CONST[1])
            self.assertTrue(strictly_non_reactive(anc))
            if anc[0](Y0) == BASE.act2(Y0):
                anchors.append(anc)
        self.assertEqual(len(anchors), 2)
        off_own_key = (((), (False, True)), False)
        self.assertNotEqual(anchors[0][0](off_own_key), anchors[1][0](off_own_key))
        state_index = {y: i for i, y in enumerate(STATES)}
        for outputs in product(B, repeat=len(STATES)):
            replacement = (lambda y, outputs=outputs: dirac(outputs[state_index[y]]), R1[1])
            laws = [prefix_law(open_loop(BASE, replacement, anc), Y0, 6) for anc in anchors]
            self.assertEqual(laws[0], laws[1])
            self.assertTrue(all(not s2(y) for w in laws[0] for y in w))
        # Removing baseline agreement destroys the conclusion, even for a strict anchor.
        self.assertNotEqual(prefix_law(open_loop(BASE, R1, ANCHOR_CONST), Y0, 3),
                            prefix_law(open_loop(BASE, R1, ANCHOR_EXTRACT), Y0, 3))

    def test_strict_autonomous_off_support_difference_stochastic_crosscheck(self):
        """Additional finite stochastic cross-check; the Lean obstruction is
        deliberately claimed only for its deterministic recording-update scope."""
        anchors = [
            (lambda y, q=q: ({False: ONE} if not s2(y) else {False: q, True: ONE-q}),
             ANCHOR_CONST[1]) for q in (F(1, 4), F(3, 4))]
        replacement = (lambda y: {False: F(1, 3), True: F(2, 3)},
                       lambda y, a, x: {False: HALF, True: HALF})
        for anc in anchors:
            self.assertTrue(strictly_non_reactive(anc))
            self.assertEqual(anc[0](Y0), BASE.act2(Y0))
        self.assertNotEqual(anchors[0][0]((((), (False, True)), False)),
                            anchors[1][0]((((), (False, True)), False)))
        for horizon in range(1, 5):
            laws = [norm(prefix_law(open_loop(BASE, replacement, anc), Y0, horizon))
                    for anc in anchors]
            self.assertEqual(laws[0], laws[1])
            self.assertGreater(len(laws[0]), 1)  # not an accidentally deterministic fixture

    def test_endogenous_common_state_is_not_opponent_locked(self):
        """A factorized anchor can still respond via s0 <- a1. Baseline-support
        agreement and local strictness alone permit divergence; IsExogenousCommon
        must reject this apparent strict MA2 witness."""
        states = [((c, (i, j)), x) for c, i, j, x in product(B, repeat=4)]
        start = ((False, (False, False)), False)
        game = BASE.with_(up0=lambda y, a, x: dirac(a[0]))
        const = ANCHOR_CONST
        public = (lambda y: dirac(y[0][0]), ANCHOR_CONST[1])
        self.assertFalse(exogenous_common(game, states))
        self.assertTrue(exogenous_common(game.with_(up0=lambda y, a, x: dirac(not y[0][0])), states))
        support = reachable(game, start, 6)
        self.assertEqual(support, {start})
        for anc in (const, public):
            self.assertTrue(strictly_non_reactive(anc, states))
            for y in support:
                self.assertEqual(anc[0](y), game.act2(y))
                for a in ACTIONS:
                    for x in B:
                        self.assertEqual(anc[1](y, a, x), game.up2(y, a, x))
        self.assertEqual(psi(open_loop(game, R1, const), start), ZERO)
        self.assertEqual(psi(open_loop(game, R1, public), start), ONE)


class ProductSubclassTests(unittest.TestCase):

    CORR = {(True, True): HALF, (False, False): HALF}

    def test_ma3_correlated_law_not_product_exact(self):
        """A Bool x Bool probability law is a product iff it equals the product of
        its own marginals; correlatedLaw is not (Lean: correlatedLaw_ne_prod, by a
        different singleton argument)."""
        def is_product(law):
            p1 = sum((v for (a, _), v in law.items() if a), ZERO)
            q1 = sum((v for (_, b), v in law.items() if b), ZERO)
            prodlaw = prod({True: p1, False: 1 - p1}, {True: q1, False: 1 - q1})
            return all(prodlaw.get(k, ZERO) == law.get(k, ZERO) for k in ACTIONS)
        self.assertFalse(is_product(self.CORR))
        self.assertTrue(is_product(prod({True: HALF, False: HALF}, {True: HALF, False: HALF})))

    def test_ma3_product_misrepresents_coordination(self):
        corr = BASE.with_(joint_action=lambda y: self.CORR, world=lambda y, a: dirac(a[0]))
        indep = BASE.with_(act1=lambda y: {True: HALF, False: HALF},
                           act2=lambda y: {True: HALF, False: HALF},
                           world=lambda y, a: dirac(a[0]))
        coord = lambda G: event_prob(prefix_law(G, Y0, 1), lambda w: s1(w[1]) == s2(w[1]))
        self.assertEqual((coord(corr), coord(indep)), (ONE, HALF))

    def test_ma3_shared_source_is_representable(self):
        """A public coin drawn by U0 into s0 and read by both players gives
        coordination 1 with every kernel in product form: correlation through S0
        is inside the subclass."""
        coin = Game(act1=lambda y: dirac(y[0][0]), act2=lambda y: dirac(y[0][0]),
                    up0=lambda y, a, x: {True: HALF, False: HALF},
                    up1=lambda y, a, x: dirac(a[0]), up2=lambda y, a, x: dirac(a[1]),
                    world=lambda y, a: dirac(a[0]))
        y0c = ((False, (False, False)), False)
        law = prefix_law(coin, y0c, 2)
        self.assertEqual(event_prob(law, lambda w: s1(w[2]) == s2(w[2])), ONE)
        self.assertEqual(event_prob(law, lambda w: s1(w[2])), HALF)


class FeasibilityAndWorldTests(unittest.TestCase):

    def test_infeasible_anchor_excluded_separate_toy(self):
        """SEPARATE toy (the F1.4 Boolean witness has no feasibility constraint):
        x' = a1 or a2 (depleted if anyone extracted); nobody may extract when
        x = True. Baseline and CL respect it; the menu builder keeps only anchors
        whose actions are feasible on every OL-reachable state."""
        feasible = lambda y: {False} if xw(y) else {True, False}
        G = Game(act1=lambda y: dirac(False),
                 act2=lambda y: dirac(s1(y) and not xw(y)),       # feasible copy
                 up0=lambda y, a, x: dirac(()),
                 up1=lambda y, a, x: dirac(a[0]), up2=lambda y, a, x: dirac(a[1]),
                 world=lambda y, a: dirac(a[0] or a[1]))
        r1 = (lambda y: dirac(not xw(y)), lambda y, a, x: dirac(a[0]))
        guarded = (lambda y: dirac(not xw(y)), lambda y, a, x: dirac(a[1]))
        always = (lambda y: dirac(True), lambda y, a, x: dirac(a[1]))
        H = 4

        def ok(Gi, who):
            return all(set(who(z)) <= feasible(z) for z in reachable(Gi, Y0, H))

        self.assertTrue(ok(G, G.act1) and ok(G, G.act2))                    # baseline
        self.assertTrue(ok(closed_loop(G, r1), r1[0]) and ok(closed_loop(G, r1), G.act2))
        menu = [a for a in (ANCHOR_CONST, guarded, always)
                if ok(open_loop(G, r1, a), a[0])]
        self.assertEqual(len(menu), 2)
        self.assertNotIn(always, menu)
        for a in menu:
            self.assertTrue(ok(open_loop(G, r1, a), r1[0]))                  # player 1 too
            self.assertTrue(is_protocol(open_loop(G, r1, a), G, r1, menu))
        self.assertFalse(is_protocol(open_loop(G, r1, always), G, r1, menu))

    def test_intervention_changing_world_is_not_a_protocol(self):
        """Mirrors protocol_world_eq / protocol_admissible_cases: CL and OL are
        accepted; an edit of P is rejected (U0 edits: see the clock test), and the
        P-edit also changes the OL value."""
        menu = [ANCHOR_CONST, ANCHOR_WORLD, ANCHOR_EXTRACT]
        cl, ol = closed_loop(BASE, R1), open_loop(BASE, R1, ANCHOR_WORLD)
        ol_badP = ol.with_(world=lambda y, a: dirac(False))
        self.assertTrue(is_protocol(cl, BASE, R1, menu))
        self.assertTrue(is_protocol(ol, BASE, R1, menu))
        self.assertFalse(is_protocol(ol_badP, BASE, R1, menu))
        self.assertEqual((psi(ol), psi(ol_badP)), (ONE, ZERO))
        not_in_menu = open_loop(BASE, R1, (lambda y: dirac(not xw(y)), ANCHOR_CONST[1]))
        self.assertFalse(is_protocol(not_in_menu, BASE, R1, menu))
        # menu action with a non-menu update; wrong player-1 replacement; correlated override
        mixed = open_loop(BASE, R1, (ANCHOR_CONST[0], lambda y, a, x: dirac(not a[1])))
        self.assertFalse(is_protocol(mixed, BASE, R1, menu))
        wrong_r1 = closed_loop(BASE, (lambda y: dirac(False), R1[1]))
        self.assertFalse(is_protocol(wrong_r1, BASE, R1, menu))
        corr = cl.with_(joint_action=lambda y: {(True, True): ONE})
        self.assertFalse(is_protocol(corr, BASE, R1, menu))

    def test_openloop_self_is_closed_loop(self):
        """Mirrors openLoop_self: the baseline opponent as 'anchor' gives CL."""
        ol_self = open_loop(BASE, R1, (BASE.act2, BASE.up2))
        self.assertEqual(psi(ol_self), psi(closed_loop(BASE, R1)))
        self.assertFalse(strictly_non_reactive((BASE.act2, BASE.up2)))


class ClockTests(unittest.TestCase):

    def test_nonstationary_anchor_needs_clock_in_baseline(self):
        """The clock must be declared in the BASELINE S0/U0 (protocols never change
        U0). Augmenting the baseline leaves z0, z_CL, z_OL unchanged; a clock-only
        (strictly non-reactive) anchor is then an admissible OL anchor; projected
        to the unaugmented state, its run visits the same state at t = 1 and t = 2
        with different successors, so no stationary kernel on the unaugmented
        state reproduces it."""
        clock_up0 = lambda y, a, x: dirac(min(y[0][0] + 1, 2))
        BC = BASE.with_(up0=clock_up0)
        y0c = ((0, (False, False)), False)
        for G0, Gc in ((BASE, BC),):
            self.assertEqual(psi(G0), psi(Gc, y0c))
            self.assertEqual(psi(closed_loop(G0, R1)), psi(closed_loop(Gc, R1), y0c))
            self.assertEqual(psi(open_loop(G0, R1, ANCHOR_CONST)),
                             psi(open_loop(Gc, R1, ANCHOR_CONST), y0c))
        timed = (lambda y: dirac(y[0][0] >= 2), lambda y, a, x: dirac(a[1]))
        cstates = [((c, (b1, b2)), x) for c in (0, 1, 2) for b1, b2, x in product(B, B, B)]
        self.assertTrue(strictly_non_reactive(timed, cstates))
        r_never = (lambda y: dirac(False), lambda y, a, x: dirac(a[0]))
        run = open_loop(BC, r_never, timed)
        self.assertTrue(is_protocol(run, BC, r_never, [timed], cstates))
        # adding the clock INSIDE an intervention (editing U0) is not a protocol of BASE
        self.assertFalse(is_protocol(open_loop(BC, r_never, timed), BASE, r_never, [timed],
                                     cstates))
        path = single_path(run, y0c, 3)
        proj = [z[0][1] + (z[1],) for z in path]
        self.assertEqual(proj[1], proj[2])
        self.assertEqual(proj[1], proj[0])
        self.assertNotEqual(proj[3], proj[2])     # same state, different successor


class DirectionVersusGapTests(unittest.TestCase):

    def test_v20_29_bounds_and_equality_cases_on_random_games(self):
        """The two-sided bound and the equality clauses are metric identities
        (arithmetic sanity checks). The checks that can fail are: psi computed from
        path laws equals an INDEPENDENT state-distribution iteration, openLoop_self,
        and non-degeneracy (OL differs from CL somewhere; an equality case with a
        nonzero effect is hit)."""
        rng = random.Random(20261017)

        def rlaw():
            p = F(rng.randint(0, 8), 8)
            return {True: p, False: 1 - p}

        eq_cases, ol_ne_cl, nonzero_eq = 0, 0, 0

        def psi_by_distribution(G, y, horizon):
            mu = {y: ONE}
            for _ in range(horizon):
                nxt = {}
                for u, p in mu.items():
                    for z, q in G.step(u).items():
                        nxt[z] = nxt.get(z, ZERO) + p * q
                mu = nxt
            return sum((p for z, p in mu.items() if s2(z)), ZERO)
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
            for y in STATES:
                z0 = psi(G, y, 3)
                zc, zo = psi(closed_loop(G, r), y, 3), psi(open_loop(G, r, anc), y, 3)
                dc, do, gap = abs(zc - z0), abs(zo - z0), abs(zc - zo)
                self.assertLessEqual(abs(dc - do), gap)
                self.assertLessEqual(gap, dc + do)
                self.assertEqual(zc, psi_by_distribution(closed_loop(G, r), y, 3))
                self.assertEqual(zo, psi_by_distribution(open_loop(G, r, anc), y, 3))
                ol_ne_cl += zc != zo
                if do == 0:
                    self.assertEqual(gap, dc); eq_cases += 1; nonzero_eq += dc != 0
                if dc == 0:
                    self.assertEqual(gap, do); eq_cases += 1; nonzero_eq += do != 0
                self.assertEqual(psi(open_loop(G, r, (G.act2, G.up2)), y, 3), zc)
        self.assertGreater(eq_cases, 0)
        self.assertGreater(ol_ne_cl, 100)
        self.assertGreater(nonzero_eq, 0)

    def test_direction_not_determined_by_gap(self):
        """For the SAME protocol pair (CL vs OL with ANCHOR_CONST), Δ_CL > Δ_OL at
        one state and Δ_CL < Δ_OL at another; on B = {s1 = False} the margins
        differ and the uniform gap bounds their difference with equality."""
        cl, ol = closed_loop(BASE, R1), open_loop(BASE, R1, ANCHOR_CONST)
        gaps_by_sign = {}
        for y in STATES:
            z0, zc, zo = psi(BASE, y), psi(cl, y), psi(ol, y)
            if abs(zc - z0) != abs(zo - z0):
                gaps_by_sign.setdefault(abs(zc - z0) > abs(zo - z0), set()).add(abs(zc - zo))
        self.assertEqual(set(gaps_by_sign), {True, False})
        # the same gap value occurs with both signs: A does not determine the direction
        self.assertTrue(gaps_by_sign[True] & gaps_by_sign[False])
        Bset = [y for y in STATES if not s1(y)]
        dcs = [abs(psi(cl, y) - psi(BASE, y)) for y in Bset]
        dos = [abs(psi(ol, y) - psi(BASE, y)) for y in Bset]
        gaps = [abs(psi(cl, y) - psi(ol, y)) for y in Bset]
        self.assertNotEqual(min(dcs), min(dos))
        self.assertLessEqual(abs(min(dcs) - min(dos)), max(gaps))
        self.assertEqual(abs(min(dcs) - min(dos)), max(gaps))


if __name__ == "__main__":
    unittest.main()

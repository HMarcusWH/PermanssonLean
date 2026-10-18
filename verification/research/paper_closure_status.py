"""Build a conservative 42-target crosswalk without rewriting the supplied spec.

Local compiler observations are kept separate from mathematical coverage and
genuine source-bound acceptance. This script never promotes a target to accepted.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

from paper_closure_analytic_audit import declarations

ROOT = Path(__file__).resolve().parents[2]
# Paths are implementation inventories, not assertions of complete coverage.
TRACKS = {
    'X1-N01': ('X1/InterventionNumerics X1/InterventionNumericalBridge X1/ExactMatrixTables',
               'All eight fixed actual typed kernels and2592 supplied literal matrix entries; source-bound eight-declaration matrix audit and corrupted-literal semantic rejection. No general intervention-family extension.'),
    'X1-N02': ('X1/InterventionNumericalBridge X1/ExactTerminalTables',
               'Fixed emitted literals and all-horizon semantic recursion; external JSON decoding is outside Lean.'),
    'X1-N03': ('X1/ExactMargins', 'Six original margins on the complete nine-start comparison.'),
    'X1-S01': ('StrategicWorld/ActionTrace* StrategicWorld/InformationBoundary Games/* X1/FullStrategy* X1/Strategy*',
               'Complete observed nonanticipating histories; independent current opponent draw; both-player literal original full-law adapter, actual fair-matching separation and no-copy information boundary.'),
    'F1-MA2': ('MultiAgent/Autonomous* MultiAgent/StrictMA2Obstruction',
               'Finite autonomous strict-subclass impossibility and standard-Borel all-time AE extension for every stationary treated mechanism. Primitive opponent-action and update agreement is required under actual baseline time/input laws, retaining the realized opponent action. Nonatomic continuum and exceptional-point counterexamples checked;78-declaration audit. History-dependent treated mechanisms remain separate.'),
    'E1-G01': ('Probability/ProjectedCommonSubkernel Quotient/GeometricPrefix Quotient/GeometricQuotient',
               'Measurable common-mass profile with explicit countable-or-countably-generated instance; no projected Markov assumption.'),
    'A3-K01': ('Probability/CouplingDualBound Probability/FiniteTransportSeparation Probability/FiniteKantorovichDuality Probability/FiniteTransportRegression Probability/FirstMoment* Probability/FiniteLipschitzExtension Probability/FinitePartition*',
               'Genuine arbitrary-real finite transport duality and optimal finite coupling existence;39-declaration audit. Explicit measurable finite quantization, bounded Lipschitz extension and normalized restricted-cell product lifts prove literal original coupling-infimum/dual-supremum equality for all separable Borel pseudometric first-moment laws;72-declaration audit. Actual countable gluing and measurable summable-step limits establish the complete first-moment metric space;60-declaration audit. General optimal-plan attainment is not inferred.'),
    'A3-I01': ('Perturbation/FiniteInvariantConstructor Perturbation/FirstMoment* Perturbation/GeneratedInvariantPerturbation',
               'Actual Banach invariant constructor, first-moment uniqueness, original kernel-iterate geometric coupling bound and metric convergence on complete separable Borel metric spaces. Moment preservation has a derived row-drift criterion. The two-kernel Banach wrapper supplies both strict contraction gates;26-declaration audit. Separate regenerative wrappers construct perturbed invariant laws without a perturbed-contraction premise.'),
    'A3-C01': ('Perturbation/DirectDualContraction Perturbation/DobrushinContraction Perturbation/FiniteStateMetricContraction Perturbation/FiniteMetricProtocol',
               'Exact global test-image criterion, finite Dobrushin/Doeblin contraction and metric stage-coupling certificates. Weighted-state and original product-max metrics are distinguished by the positive minimum-weight conversion. Four strict numeric gates independently generate all four invariant laws.'),
    'A3-F01': ('Perturbation/FiniteOccupation* Perturbation/Regenerative* Perturbation/FirstMomentOccupationProperty Probability/Regenerative* Probability/L1* Probability/FirstMomentEmpirical* Probability/FirstMomentTopology Probability/FiniteQuantizationBound Probability/CesaroShiftInvariant MultipleLimit/Regenerative* MultipleLimit/CanonicalShiftLaw',
               'Finite kernel-independent occupation functional plus nonfinite geometric regeneration. Constructed invariant, Poisson resolvent and bounded-innovation strong law give all-initial bounded averages and noncompact weak empirical convergence;87-declaration audit. An explicit expected absolute regenerative reward series supplies descriptor first moments. Derived L1 maximal approximation, actual stationary shift preservation and regenerated common-mass transfer give all-initial integrable nonnegative averages. Countable quantizer errors/cell averages give genuine empirical W1 convergence and uniform excess-tail control. A fixed global P1-valued limit/fallback and bounded continuous functional supply all four actual original path factorizations and full margin adapter. The original global dual-Lipschitz functional and baseline contraction gates remain explicit; arbitrary frozen properties and an unrestricted weak-only selector are not inferred.'),
    'A3-P01': ('Perturbation/PrimitiveMetricBudget Probability/FiniteRowCoupling Perturbation/FiniteSequentialCoupling Perturbation/FiniteTypedRows Perturbation/FinitePrimitiveMetric Perturbation/FiniteMetricCouplingFixture',
               'Actual finite conditional couplings in the literal alpha/P/U order, exact marginals and propagated weighted metric sensitivities. Derived budget is a*deltaU+(b+a*LUx)*deltaP+(a*LUa+(b+a*LUx)*LPa)*deltaAlpha. Original product-max conversion and nonzero weighted fixtures retained; combined metric audit84 declarations. This finite implementation is within the supplied primitive-metric scope.'),
    'D2-R01': ('ReverseSolver/*Monitor* ReverseSolver/ResidenceSpecializationOptimality ReverseSolver/RollingResidenceTable',
               'Literal retryable residence with real behavioral histories and deterministic attainment. Rolling tables checked; no bit-complexity theorem.'),
    'A2-P01': ('Perturbation/PrimitiveProductTV',
               'Actual ordered measurable primitive common-mass product; every primitive row is quantified.'),
    'A2-P02': ('Probability/LocalizedHistoryTV',
               'Actual first-history-law averaged defects plus initial mismatch. Quantitative visit budgets must be separately supplied for each process.'),
    'E1-P01': ('Probability/SummablePathScores Probability/DiscountedInitialBudget Probability/CylinderTotalVariation Probability/DependentHistoryCommonMass Probability/FullPathProduct*',
               'Summable bounded output-score integrals and exact normalized discount budgets, including initial mismatch and time-zero weight;4-declaration initial-budget audit. Constructed dependent-history common mass retains initial mismatch and time-varying finite products; summable defects give a genuine infinite product. Actual infinite laws are linked by literal prefix marginal identifications, and generating-cylinder algebra approximation proves full-path event TV;43-declaration audit. Fixed recurring positive leakage is nonsummable and its finite budget tends to1; survival transfer is not inferred.'),
    'E1-P02': ('Quotient/GeometricMargin',
               'Original finite-prefix margin and independent Exact-GR certificates. Bidirectional gap and grounded/confirmatory wrappers retain independent original gates.'),
    'F1-P01': ('MultiAgent/PlayerTwoProtocols MultiAgent/PlayerSwap*',
               'Measurable-general direct player-two CL/OL construction. Finite-space asymmetric coordinate pullback, actual original full laws and original paired margins follow the supplied finite-sum swap profile. Comparison and property matching remain explicit.'),
    'F1-P02': ('MultiAgent/FiniteProduct* MultiAgent/Measurable*',
               'Finite index with arbitrary measurable coordinate/input spaces, actual Giry-measurable product kernels, selected-player protocols and generic measurable binary-product equivalence. Actual three-player real-coordinate regression distinguishes closed/open-loop anchors, preserves physical/common kernels and checks empty-index normalization;48-declaration audit.'),
    'F1-P03': ('MultiAgent/PrivateClock* MultiAgent/NatPrivateClock* MultiAgent/MeasurableNat* MultiAgent/ChronologicalPathLaw',
               'Actually updated finite-phase and genuine natural-number private clocks, with arbitrary declared Nat anchor schedules. General measurable countable schedule selection and whole-measure product transport remove original-coordinate finiteness/countability assumptions. Literal action/world/update rows, clock successor, inherited strictness/exogeneity/feasibility and original chronological full infinite-law projection retain the a(t+n) schedule from fixed initial clock t. A real-coordinate nonperiodic fixture checks the general profile. Frozen original baselines are not silently enlarged.'),
    'F1-P04': ('MultiAgent/FeasibleAnchors',
               'Full own-key fibre intersection criterion for actual strict mechanisms, plus fixed-order finite selector. Joint nonrectangular feasibility is separate.'),
    'F1-P05': ('MultiAgent/BehavioralAutonomy',
               'Actual all-history/all-legal-control unmarked projected-row iff. Marked strengthening and causal inference from observational laws are separate.'),
    'F1-P06': ('MultiAgent/CorrelatedMediator',
               'Finite sampled joint mediator and exact mixture-of-deterministic-products representation. No exogeneity or public-information conclusion.'),
    'F1-P07': ('MultiAgent/FiniteMediation',
               'Finite conditional-product-noise SCM with normalized assignment, observational conditional identification, signed decomposition and two complete observationally equivalent but interventionally different SCM records checked. Dynamic sequential identification remains separate.'),
    'D2-P01': ('ReverseSolver/FiniteMonitor ReverseSolver/BehavioralFinitePolicy ReverseSolver/Chronological* ReverseSolver/MonitorOptimality ReverseSolver/MonitorEventOptimality',
               'Real behavioral fully observed finite terminal monitor reward and actual deterministic attainer.'),
    'D2-P02': ('ReverseSolver/FirstEntryMonitor ReverseSolver/ResidenceSpecializationOptimality',
               'Literal first-ever-hit semantics, irreversible failed attempt and behavioral optimum.'),
    'D2-P03': ('ReverseSolver/AvoidResidence* ReverseSolver/ResidenceSpecializationOptimality ReverseSolver/ThroughHorizonRisk*',
               'Literal completion before danger, danger precedence, original deterministic-law and behavioral-optimum bridges. A separate ever-danger flag continues after completed success; its actual through-horizon event probability equals the occupancy LP terminal linear risk score for every admitted real history controller. Time-zero, tied and after-success danger are distinguished.'),
    'D2-P04': ('ReverseSolver/SolverBoundaryWitnesses ReverseSolver/Polytope* ReverseSolver/Flow* ReverseSolver/FiniteOccupancy*',
               'Total exact rational active-subset/Gram/Cramer solver, actual real-vertex completeness, derived compact flow polytope, all-real full-history policy/flow equivalence and simultaneous legal x/d reconstruction. Returned actual controller attains risk-constrained optimum; none certifies infeasibility against the same policy class. Actual success17/20/risk1/20 fixture and221-declaration audit checked. Efficiency and optional dynamic dual checker remain separate.'),
    'D2-P05': ('ReverseSolver/Rectangular* ReverseSolver/SolverBoundaryWitnesses ReverseSolver/PrivateControlStage*',
               'Nature-after-realized-control rectangular dynamic game with actual normalized chronological law. Separate total rational private-draw stage LP dominates all real control mixtures, guarantees against every real mixed nature law, and has actual pure nature attainer;59-declaration audit. Matching/opposite timing distinction and negative-payoff floor checked. Whole-horizon model commitment is not row rectangularity.'),
    'D2-P06': ('ReverseSolver/Belief*',
               'Finite full hidden augmented-state Bayes filter, zero-probability default, alpha-vector envelope and actual optimal observation-history law;116-declaration audit. Actual hidden monitor memory and literal physical/control chronology are retained. Hidden-state peek regression rejects information leakage. Arbitrary real finite argmax is mathematical attainment, without an executable real-number optimization claim.'),
    'D2-P07': ('ReverseSolver/InfiniteSafety* ReverseSolver/BehavioralInfiniteLaw ReverseSolver/GreatestControlledInvariant',
               'Actual canonical infinite safety probability for all real full-history behavioral controllers; one deterministic stationary maximizer for all states; finite support pruning computes greatest controlled invariant set and exact probability-one region. Fixed-leakage finite-versus-infinite counterexample and15-declaration audit checked.'),
    'D2-P08': ('ReverseSolver/AdaptiveGrammarControl',
               'Actual admissible compatible alpha/P/U block menu with literal fixed world, certified rational atoms and full-history adaptive monitor optimum checked as a normalized coded finite law with an explicit measurable state equivalence. Rational atom typing is an explicit data certificate; no single frozen intervention is inferred.'),
    'D2-P09': ('ReverseSolver/StationaryOccupationObjective ReverseSolver/StationaryMenuOptimization',
               'Finite declared stationary-policy menu and actual occupation-limit expectation optimizer checked. No adaptive asymptotic policy theorem.'),
    'C11-P01': ('ReverseSolver/C11Reference*',
               'Total generic rational Cramer family for genuine bottom classes, checker soundness and typed identification checked.'),
    'C-P01': ('MultipleLimit/CanonicalBoundedInnovations MultipleLimit/CompactFeller* Probability/BoundedSquareStrongLaw Probability/BoundedInnovations Probability/HopfMaximal Probability/BoundedOrbitAverages Probability/BoundedBirkhoff* Probability/InvariantSigma MultipleLimit/Stationary* MultipleLimit/CanonicalInitial* MultipleLimit/CountableEmpiricalWeak MultipleLimit/PolishStationaryRandomOccupation MultipleLimit/NonfiniteClock MultipleLimit/GrowingBlock*',
               'Actual all-initial compact Feller cluster/unique-invariant weak convergence;88-declaration audit. Bounded pointwise ergodic and invariant-sigma conditional-expectation identity without invertibility/ergodicity;47-declaration audit. Actual standard-Borel conditional random invariant law, compact/noncompact second-countable metric stationary weak empirical limits and exact whole-path initial Radon-Nikodym formula;68-declaration audit. Genuine homogeneous countable clock escaping-mass and fixed-descriptor growing-block nonconvergence;33-declaration audit. No unrestricted nonfinite occupation theorem or integrable-unbounded Birkhoff extension is inferred.'),
    'B-P01': ('GrammarRobust/CompatibleOverlap GrammarRobust/Overlap*',
               'Compatible measurable row replacements, actual fixed-P models, original admissible intervention effects and margins.'),
    'B-P02': ('GrammarRobust/LowerSetTransport GrammarRobust/OriginalLowerSetTransport',
               'Generic local lower-set theorem, positive finite meet closure, and original-margin instantiation checked. Full lower coverage is explicit.'),
    'X1-P01': ('EconomicWitness/*',
               'Separate constructed three-world economic witness. Original Exact-GR, grounded confirmatory uniform PR and margin1; initial-law trace bridge and92-declaration audit checked.'),
    'APP-E01': ('Specialized/SeamReduction',
               'Real symmetric seam rank2, extra constant-diagonal rank1, actual feature effect and original margin. A natural specialized model realization remains external.'),
    'APP-E02': ('Specialized/FiniteDetection Specialized/BoundaryWitnesses',
               'Legal quantitative approximation, two source controls, persistence and actual feature-effect wrapper. Source legality/dictionary bridge remains explicit.'),
    'APP-E03': ('Specialized/ShellSchur Specialized/ShellResolvent Specialized/BoundaryWitnesses',
               'Finite PSD negative shift, genuine inverse, determinant and two-way shell equations with actual shell dimension; genuine arbitrary-core resolvent and scalar-shell derivative. Source hierarchy adapters remain explicit.'),
    'APP-E04': ('Specialized/SingularCompatibility',
               'Finite range/kernel compatibility, completed square, incompatible null witness and denominator-free source transport. Actual negative-resolvent kernel projection checked; source realizations remain explicit.'),
    'APP-E05': ('Specialized/GramSeparation',
               'Explicit Gram gap witness and operator threshold, masking budget and actual feature effect. Signed source representation remains an explicit bridge.'),
}


def main():
    spec = json.loads((ROOT / 'research/paper_closures/spec/registries/closure_contracts.json').read_text())
    root_code = re.sub(r'/\-.*?\-/|--[^\n]*', '',
                       (ROOT / 'PermanssonResearch.lean').read_text(), flags=re.S)
    imported = {module for line in root_code.splitlines() if line.startswith('import ')
                for module in line[7:].split()}
    assert set(TRACKS) == {row['atlas_id'] for row in spec['contracts']}
    rows = []
    for contract in spec['contracts']:
        patterns, boundary = TRACKS[contract['atlas_id']]
        paths = set()
        for pattern in patterns.split():
            paths.update((ROOT / 'PermanssonResearch').glob(pattern + '.lean'))
        sources = []
        for path in sorted(paths):
            relative = path.relative_to(ROOT).as_posix()
            module = relative.removesuffix('.lean').replace('/', '.')
            if module not in imported:
                continue
            log = ROOT / '.lake/closure-build' / (module + '.json')
            artifact = ROOT / '.lake/build/lib/lean' / relative.replace('.lean', '.olean')
            observation = json.loads(log.read_text()) if log.is_file() else None
            fresh = artifact.is_file() and artifact.stat().st_mtime_ns >= path.stat().st_mtime_ns
            sources.append({'source': relative, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                            'named_exports': declarations(path.read_text(encoding='utf-8-sig')),
                            'local_compiler_observation': observation, 'artifact_fresh': fresh})
        rows.append({'atlas_id': contract['atlas_id'], 'title': contract['title'],
                     'selected_scope_as_supplied': contract['selected_scope'],
                     'acceptance_status': 'NOT_ACCEPTED',
                     'implementation_status': 'LOCAL_IMPLEMENTATION_WITH_EXPLICIT_BOUNDARY' if sources else 'OPEN',
                     'implementation_boundary_and_residual': boundary, 'sources': sources})
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    dirty = bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT))
    report = {'format': 'Permansson.PaperClosureImplementationCrosswalk.v1',
              'reference_B': spec['source_commit'], 'recording_head': head,
              'recording_worktree_dirty': dirty, 'target_count': len(rows),
              'overall_status': 'SELECTED_IMPLEMENTATIONS_RECORDED_BROADER_ATLAS_SCOPED',
              'acceptance_boundary': 'Local proof observations do not certify all mathematical coverage, '
                                     'PR-head/synthetic-merge CI, or independent statement-scope acceptance.',
              'targets': rows}
    out = ROOT / 'research/paper_closures/implementation_status.json'
    out.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print('Wrote conservative implementation crosswalk:', len(rows), 'targets;', out)


if __name__ == '__main__':
    main()

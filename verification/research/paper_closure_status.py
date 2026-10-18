"""Build a conservative 42-target crosswalk without rewriting the supplied spec.

Local compiler observations are kept separate from mathematical coverage and
genuine source-bound acceptance. This script never promotes a target to accepted.
"""
import hashlib
import json
from pathlib import Path
import subprocess

from paper_closure_analytic_audit import declarations

ROOT = Path(__file__).resolve().parents[2]
# Paths are implementation inventories, not assertions of complete coverage.
TRACKS = {
    'X1-N01': ('X1/InterventionNumerics X1/InterventionNumericalBridge',
               'All eight fixed actual typed kernels; no general intervention-family extension.'),
    'X1-N02': ('X1/InterventionNumericalBridge X1/ExactTerminalTables',
               'Fixed emitted literals and all-horizon semantic recursion; external JSON decoding is outside Lean.'),
    'X1-N03': ('X1/ExactMargins', 'Six original margins on the complete nine-start comparison.'),
    'X1-S01': ('StrategicWorld/ActionTrace* Games/* X1/FullStrategy* X1/Strategy*',
               'Complete observed nonanticipating histories; independent current opponent draw; both-player literal original full-law adapter and current149-declaration audit.'),
    'F1-MA2': ('MultiAgent/Autonomous* MultiAgent/StrictMA2Obstruction',
               'Finite autonomous strict-subclass impossibility. Standard-Borel all-time AE extension remains open.'),
    'E1-G01': ('Probability/ProjectedCommonSubkernel Quotient/GeometricPrefix Quotient/GeometricQuotient',
               'Measurable common-mass profile with explicit countable-or-countably-generated instance; no projected Markov assumption.'),
    'A3-K01': ('Probability/CouplingDualBound',
               'Weak coupling-to-dual direction and genuine finite product coupling. Finite reverse duality, Polish quantization and completeness remain open.'),
    'A3-I01': ('Perturbation/FiniteInvariantConstructor',
               'Finite invariant construction/dual contraction profile checked. General first-moment complete-space construction remains open.'),
    'A3-C01': ('Perturbation/DirectDualContraction',
               'Exact global test-image criterion; constant refresh and identity examples. Dobrushin and metric row-coupling certificate interfaces remain separate.'),
    'A3-F01': ('Perturbation/FiniteOccupation*',
               'Finite kernel-independent actual occupation functional and four-kernel adapter checked. Nonfinite regenerative profile remains open.'),
    'A3-P01': ('Perturbation/PrimitiveMetricBudget',
               'Bounded-diameter actual primitive certificate only. Weighted metric sensitivities and conditional metric stage couplings remain open.'),
    'D2-R01': ('ReverseSolver/*Monitor* ReverseSolver/ResidenceSpecializationOptimality ReverseSolver/RollingResidenceTable',
               'Literal retryable residence with real behavioral histories and deterministic attainment. Rolling tables checked; no bit-complexity theorem.'),
    'A2-P01': ('Perturbation/PrimitiveProductTV',
               'Actual ordered measurable primitive common-mass product; every primitive row is quantified.'),
    'A2-P02': ('Probability/LocalizedHistoryTV',
               'Actual first-history-law averaged defects plus initial mismatch. Quantitative visit budgets must be separately supplied for each process.'),
    'E1-P01': ('Probability/SummablePathScores',
               'Summable bounded output-score integrals and geometric scalar budget. Infinite-product full-TV extension is open; survival is not inferred.'),
    'E1-P02': ('Quotient/GeometricMargin',
               'Original finite-prefix margin and independent Exact-GR certificates. Bidirectional gap and grounded/confirmatory wrappers retain independent original gates.'),
    'F1-P01': ('MultiAgent/PlayerTwoProtocols MultiAgent/PlayerSwap*',
               'Actual asymmetric coordinate pullback, original full laws and original paired margins. Comparison and property matching remain explicit.'),
    'F1-P02': ('MultiAgent/FiniteProduct*',
               'Actual finite-coordinate product kernels, selected-player protocols and n=2 original-law reduction checked. Arbitrary measurable coordinates remain separate.'),
    'F1-P03': ('MultiAgent/PrivateClock* MultiAgent/ChronologicalPathLaw',
               'Actually updated private clock and canonical infinite-law projection bridge checked.'),
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
    'D2-P03': ('ReverseSolver/AvoidResidence* ReverseSolver/ResidenceSpecializationOptimality',
               'Literal completion before danger, danger precedence, original deterministic-law and behavioral-optimum bridges.'),
    'D2-P04': ('ReverseSolver/SolverBoundaryWitnesses',
               'Boundary counterexample only. Exact rational occupancy-polytope solver, reconstruction and vertex optimum remain open.'),
    'D2-P05': ('ReverseSolver/Rectangular* ReverseSolver/SolverBoundaryWitnesses',
               'Nature-after-realized-control rectangular game with actual normalized chronological law. Private-control-draw stage LP remains open.'),
    'D2-P06': ('', 'Finite hidden augmented-state belief update, alpha-vector construction and optimality remain open.'),
    'D2-P07': ('', 'Infinite safety optimum, stationary attainment and greatest controlled invariant construction remain open.'),
    'D2-P08': ('ReverseSolver/AdaptiveGrammarControl',
               'Actual admissible compatible alpha/P/U block menu with literal fixed world, certified rational atoms and full-history adaptive monitor optimum checked as a normalized coded finite law with an explicit measurable state equivalence. Rational atom typing is an explicit data certificate; no single frozen intervention is inferred.'),
    'D2-P09': ('ReverseSolver/StationaryOccupationObjective ReverseSolver/StationaryMenuOptimization',
               'Finite declared stationary-policy menu and actual occupation-limit expectation optimizer checked. No adaptive asymptotic policy theorem.'),
    'C11-P01': ('ReverseSolver/C11Reference*',
               'Total generic rational Cramer family for genuine bottom classes, checker soundness and typed identification checked.'),
    'C-P01': ('', 'Compact Feller cluster, unique-invariant convergence and stationary/AC random-law extensions remain open.'),
    'B-P01': ('GrammarRobust/CompatibleOverlap GrammarRobust/Overlap*',
               'Compatible measurable row replacements, actual fixed-P models, original admissible intervention effects and margins.'),
    'B-P02': ('GrammarRobust/LowerSetTransport GrammarRobust/OriginalLowerSetTransport',
               'Generic local lower-set theorem, positive finite meet closure, and original-margin instantiation checked. Full lower coverage is explicit.'),
    'X1-P01': ('EconomicWitness/*',
               'Separate constructed three-world economic witness. Original Exact-GR, grounded confirmatory uniform PR and margin1; initial-law trace bridge and92-declaration audit checked.'),
    'APP-E01': ('Specialized/SeamReduction',
               'Real symmetric seam rank2, extra constant-diagonal rank1, actual feature effect and original margin. A natural specialized model realization remains external.'),
    'APP-E02': ('Specialized/FiniteDetection',
               'Legal quantitative approximation, two source controls, persistence and actual feature-effect wrapper. Source legality/dictionary bridge remains explicit.'),
    'APP-E03': ('Specialized/ShellSchur Specialized/ShellResolvent',
               'Finite PSD negative shift, genuine inverse, determinant and two-way shell equations with actual shell dimension; genuine arbitrary-core resolvent and scalar-shell derivative. Source hierarchy adapters remain explicit.'),
    'APP-E04': ('Specialized/SingularCompatibility',
               'Finite range/kernel compatibility, completed square, incompatible null witness and denominator-free source transport. Actual negative-resolvent kernel projection checked; source realizations remain explicit.'),
    'APP-E05': ('Specialized/GramSeparation',
               'Explicit Gram gap witness and operator threshold, masking budget and actual feature effect. Signed source representation remains an explicit bridge.'),
}


def main():
    spec = json.loads((ROOT / 'research/paper_closures/spec/registries/closure_contracts.json').read_text())
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
                     'implementation_status': 'LOCAL_IMPLEMENTATION_WITH_EXPLICIT_BOUNDARY' if paths else 'OPEN',
                     'implementation_boundary_and_residual': boundary, 'sources': sources})
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    dirty = bool(subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT))
    report = {'format': 'Permansson.PaperClosureImplementationCrosswalk.v1',
              'reference_B': spec['source_commit'], 'recording_head': head,
              'recording_worktree_dirty': dirty, 'target_count': len(rows),
              'overall_status': 'IN_PROGRESS_NOT_ALL_42_CLOSED',
              'acceptance_boundary': 'Local proof observations do not certify all mathematical coverage, '
                                     'PR-head/synthetic-merge CI, or independent statement-scope acceptance.',
              'targets': rows}
    out = ROOT / 'research/paper_closures/implementation_status.json'
    out.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print('Wrote conservative implementation crosswalk:', len(rows), 'targets;', out)


if __name__ == '__main__':
    main()

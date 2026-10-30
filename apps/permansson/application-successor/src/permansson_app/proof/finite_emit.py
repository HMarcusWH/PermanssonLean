"""Exact finite alpha/P/U -> literal-bound Lean proof-source candidate.

This is *source emission*, not proof replay. Every model row and induced atom
is reflected as a rational Lean term. The pinned Lean compiler must check the
emitted term and axioms separately; generating it cannot confer any status.

Infeasible controls have no P/U rows in the source model. To represent a total
Lean FiniteWorldInput, this emitter supplies explicit, documented stochastic
extensions on infeasible action rows. These must never be described as
identified or observed source primitives.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..errors import AppError
from ..finite_world import FiniteWorld, induced_kernel, parse_finite_world
from ..identity import canonical_bytes
from ..strict_json import strict_read

FORMAT = "Permansson.App.FiniteWorldLeanSourceCandidate.v1"
MAX_DIM = 2
MAX_TOTAL_TERMS = 768
MAX_SOURCE_BYTES = 262144


def rational_expr(value: Fraction) -> str:
    if type(value) is not Fraction:
        raise AppError("REIFICATION_TYPE", "expected an exact rational")
    return (f"({value.numerator} : ℚ)" if value.denominator == 1 else
            f"(({value.numerator} : ℚ) / ({value.denominator} : ℚ))")


def indexed(variable: str, entries: list[str], dimension: int) -> str:
    if len(entries) != dimension or not 1 <= dimension <= MAX_DIM:
        raise AppError("REIFICATION_SCOPE", "invalid finite index dimension")
    expression = entries[-1]
    for i in range(dimension - 2, -1, -1):
        expression = (f"(if {variable} = ({i} : Fin {dimension}) then "
                      f"{entries[i]} else {expression})")
    return expression


def nested(axes: list[tuple[str, int]], leaf) -> str:
    if not axes:
        return leaf([])
    def descend(depth: int, position: list[int]):
        if depth == len(axes):
            return leaf(position)
        name, n = axes[depth]
        return indexed(name, [descend(depth + 1, [*position, i])
                              for i in range(n)], n)
    return descend(0, [])


def _terms(model: FiniteWorld):
    S, X, A = model.strategic, model.world, model.actions
    ns, nx, na = len(S), len(X), len(A)
    if any(n > MAX_DIM or n < 1 for n in (ns, nx, na)):
        raise AppError("REIFICATION_SCOPE", "literal Lean source limited to 1..2 per dimension")
    # Bound the complete number of source inputs and proved atoms, irrespective
    # of input textual size. Never enumerate an unrestricted Cartesian product.
    count = ns * nx * na * nx * ns + ns * nx * na * nx + ns * nx * na + (ns * nx) ** 2
    if count > MAX_TOTAL_TERMS:
        raise AppError("REIFICATION_SCOPE", "literal source exceeds maximum term count")
    axes3 = [('s', ns), ('x', nx), ('a', na)]
    axes4 = [*axes3, ('xp', nx)]
    axes5 = [*axes4, ('sp', ns)]
    def get_feasible(idx):
        s, x, a = idx
        return 'true' if A[a] in model.feasible[S[s], X[x]] else 'false'
    def get_alpha(idx):
        s, x, a = idx
        return rational_expr(model.alpha[S[s], X[x]][a])
    # Use a canonical self-world, self-strategic Dirac extension on each
    # unavailable (s,x,a) row; it has no source/practical policy authority.
    extensions = []
    for s in S:
        for x in X:
            for a in A:
                if a not in model.feasible[s, x]:
                    extensions.append({'s': s, 'x': x, 'a': a,
                                       'world_extension': 'dirac_same_world',
                                       'strategic_extension': 'dirac_same_strategic'})
    def get_world(idx):
        s, x, a, xp = idx
        key = (S[s], X[x], A[a])
        if A[a] in model.feasible[S[s], X[x]]:
            return rational_expr(model.P[key][xp])
        return rational_expr(Fraction(int(x == xp)))
    def get_update(idx):
        s, x, a, xp, sp = idx
        key = (S[s], X[x], A[a], X[xp])
        if A[a] in model.feasible[S[s], X[x]]:
            return rational_expr(model.U[key][sp])
        return rational_expr(Fraction(int(s == sp)))
    return ns, nx, na, extensions, {
        'feasible': nested(axes3, get_feasible),
        'alpha': nested(axes3, get_alpha),
        'world': nested(axes4, get_world),
        'update': nested(axes5, get_update),
    }


def input_definition(model: FiniteWorld, name: str = 'input') -> tuple[list[str], tuple[int, int, int], list[dict]]:
    """Lean `def input : FiniteWorldInput ...` lines with per-row proofs.

    Shared by every emitter that binds a theorem to the same reflected source,
    so the primitive rows and their extensions are never restated differently.
    """
    if type(model) is not FiniteWorld:
        raise AppError('REIFICATION_TYPE', 'parsed finite strategic-world model required')
    if not name.isidentifier() or not name.isascii():
        raise AppError('REIFICATION_TYPE', 'Lean definition name must be a plain identifier')
    ns, nx, na, extensions, terms = _terms(model)
    lines = [
        f'def {name} : FiniteWorldInput {ns} {nx} {na} where',
        f'  feasible := fun s x a => ({terms["feasible"]}) = true',
        f'  alpha := fun s x a => {terms["alpha"]}',
        f'  world := fun s x a xp => {terms["world"]}',
        f'  update := fun s x a xp sp => {terms["update"]}',
        '  alpha_nonneg := by',
        '    intro s x a',
        '    fin_cases s <;> fin_cases x <;> fin_cases a <;> norm_num',
        '  alpha_zero_of_infeasible := by',
        '    intro s x a h',
        '    fin_cases s <;> fin_cases x <;> fin_cases a <;> simp_all',
        '  world_nonneg := by',
        '    intro s x a xp',
        '    fin_cases s <;> fin_cases x <;> fin_cases a <;> fin_cases xp <;> norm_num',
        '  update_nonneg := by',
        '    intro s x a xp sp',
        '    fin_cases s <;> fin_cases x <;> fin_cases a <;> fin_cases xp <;> fin_cases sp <;> norm_num',
        '  alpha_sum_one := by',
        '    intro s x',
        '    fin_cases s <;> fin_cases x <;> norm_num [Fin.sum_univ_succ]',
        '  world_sum_one := by',
        '    intro s x a',
        '    fin_cases s <;> fin_cases x <;> fin_cases a <;> norm_num [Fin.sum_univ_succ]',
        '  update_sum_one := by',
        '    intro s x a xp',
        '    fin_cases s <;> fin_cases x <;> fin_cases a <;> fin_cases xp <;> norm_num [Fin.sum_univ_succ]',
    ]
    return lines, (ns, nx, na), extensions


def emit_source(model: FiniteWorld) -> tuple[str, dict]:
    input_lines, (ns, nx, na), extensions = input_definition(model)
    semantic = model.semantic_id()
    kernel = induced_kernel(model)
    lines = [
        'import PermanssonResearch.ApplicationBridge.FiniteWorldInput',
        'import Mathlib.Tactic',
        '',
        '/-! Exact finite application instance. Generated source only.',
        f'    Source semantic SHA-256: {semantic["sha256"]}',
        '    Infeasible P/U entries are normalized Dirac extensions.',
        '    No empirical identification, external model correspondence,',
        '    global control optimality, or release certification is asserted.',
        '-/',
        '',
        'namespace PermanssonResearch.ApplicationBridge.ReifiedFiniteWorld',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0',
        '',
        *input_lines,
        '',
        '/-- Complete finite joint-state row normalization follows from',
        '    individually reflected stochastic alpha/P/U primitives. -/',
        f'theorem induced_rows_normalized (y : Fin {ns} × Fin {nx}) :',
        f'    (∑ z : Fin {ns} × Fin {nx}, input.inducedAtom y z) = 1 :=',
        '  input.inducedAtom_sum_one y',
        '',
    ]
    # Instance-specific equalities are not `rfl`/assumed output equality:
    # each must reduce the concrete reflected primitives and rational sum.
    theorem_names = ['induced_rows_normalized']
    for i, (s, x) in enumerate((s, x) for s in range(ns) for x in range(nx)):
        for j, (sp, xp) in enumerate((sp, xp) for sp in range(ns) for xp in range(nx)):
            name = f'atom_{i}_{j}'
            theorem_names.append(name)
            lines += [
                f'theorem {name} : input.inducedAtom',
                f'    (({s} : Fin {ns}), ({x} : Fin {nx}))',
                f'    (({sp} : Fin {ns}), ({xp} : Fin {nx})) =',
                f'      {rational_expr(kernel[i][j])} := by decide +kernel',
                '',
            ]
    lines += ['end PermanssonResearch.ApplicationBridge.ReifiedFiniteWorld', '']
    for name in theorem_names:
        lines.append('#print axioms PermanssonResearch.ApplicationBridge.ReifiedFiniteWorld.' + name)
    lines.append('')
    source = '\n'.join(lines)
    if len(source.encode('utf-8')) > MAX_SOURCE_BYTES:
        raise AppError('REIFICATION_SCOPE', 'literal Lean source exceeds byte budget')
    result = {
        'format': FORMAT,
        'source_semantic_identity': semantic,
        'lean_source_sha256': sha256(source.encode('utf-8')).hexdigest(),
        'declared_lean_module': 'PermanssonResearch.ApplicationBridge.ReifiedFiniteWorld',
        'theorem_names': theorem_names,
        'number_of_induced_atoms': (ns * nx) ** 2,
        'p_u_infeasible_normalized_extensions': extensions,
        'reification_scope': {'ns': ns, 'nx': nx, 'na': na},
        'source_emitted': True,
        'lean_compiler_executed': False,
        'lean_status': 'NOT_EXECUTED',
        'independent_axiom_audit': False,
        'scientific_claims_verified': False,
        'release_authorized': False,
    }
    return source, result


def _new_directory(path: Path) -> Path:
    target = path.absolute()
    if (target.exists() or target.is_symlink() or
            any(parent.is_symlink() for parent in target.parents)):
        raise AppError('OUTPUT_SCOPE', 'output must be a new ordinary directory without symlink ancestors')
    target.mkdir(parents=True, exist_ok=False)
    return target


def emit_file(model_file: Path, directory: Path) -> dict:
    raw, value = strict_read(model_file)
    model = parse_finite_world(value)
    source, receipt = emit_source(model)
    receipt['source_bytes_sha256'] = sha256(raw).hexdigest()
    out = _new_directory(directory)
    (out / 'ReifiedFiniteWorld.lean').write_bytes(source.encode('utf-8'))
    (out / 'source_candidate.json').write_bytes(canonical_bytes(receipt) + b'\n')
    return {'source': str(out / 'ReifiedFiniteWorld.lean'),
            'receipt': str(out / 'source_candidate.json'),
            'lean_status': 'NOT_EXECUTED',
            'source_sha256': receipt['lean_source_sha256']}


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('model', type=Path)
    p.add_argument('--output', required=True, type=Path)
    args = p.parse_args(argv)
    try:
        print(json.dumps(emit_file(args.model, args.output), sort_keys=True))
        return 0
    except AppError as exc:
        print(json.dumps({'ok': False, 'error': {'code': exc.code, 'message': str(exc)}}), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())

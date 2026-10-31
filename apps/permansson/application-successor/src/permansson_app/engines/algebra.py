"""Exact finite rational real-algebra witnesses for specialized profiles.

Four profiles, each over explicit rational matrices and vectors:

* ``seam`` — symmetry and the seam equations at a pivot (rank at most two),
  with a common-mode constant when the diagonal is constant;
* ``schur`` — an exact LDLᵀ positive-semidefinite witness for ``H``, the
  solution ``X`` of ``(H − ℓ) X = B`` for ``ℓ < 0`` and the shell complement
  ``S = (C − ℓ) − Bᵀ X``;
* ``singular`` — an LDLᵀ witness for symmetric ``H`` and either a preimage
  ``x`` of ``b`` with the bordered-form gap ``c − ⟨b, x⟩`` or a kernel vector
  ``z`` with ``⟨b, z⟩ ≠ 0``;
* ``gram`` — the Gram gap, the Gram witness, the signed value and the exact
  operator-perturbation threshold.

The identification of a strategic source with these matrices (a feature or
operator map) is never established here; it remains an explicit premise.
"""
from __future__ import annotations
from fractions import Fraction
from ..errors import AppError
from ..finite_world import exact_ratio
from ..identity import semantic_identity, rational_text

REQUEST = 'Permansson.App.RationalAlgebraRequest.v1'
RECEIPT = 'Permansson.App.RationalAlgebraReceipt.v1'
MAX_N = 4
MAX_M = 3
FIELDS = {'seam': {'H', 'pivot'}, 'schur': {'H', 'B', 'C', 'ell'},
          'singular': {'H', 'b', 'c'}, 'gram': {'x', 'y', 'c'}}


def _vec(raw, n=None, label='vector'):
    if type(raw) is not list or not raw or len(raw) > MAX_N or (n is not None and len(raw) != n):
        raise AppError('ALGEBRA_INPUT', f'bad {label}')
    return [exact_ratio(v) for v in raw]


def _mat(raw, rows=None, cols=None, label='matrix', limit=MAX_N):
    if type(raw) is not list or not raw or len(raw) > limit or (rows is not None and len(raw) != rows):
        raise AppError('ALGEBRA_INPUT', f'bad {label}')
    out = [_vec(r, cols, label) for r in raw]
    if len({len(r) for r in out}) != 1:
        raise AppError('ALGEBRA_INPUT', f'ragged {label}')
    return out


def _symmetric(H):
    return all(H[i][j] == H[j][i] for i in range(len(H)) for j in range(len(H)))


def ldl(H):
    """Exact H = L diag(d) Lᵀ with unit lower L and d >= 0, or None if not PSD."""
    n = len(H)
    L = [[Fraction(int(i == j)) for j in range(n)] for i in range(n)]
    d = [Fraction(0)] * n
    for k in range(n):
        d[k] = H[k][k] - sum((L[k][j] ** 2 * d[j] for j in range(k)), Fraction(0))
        if d[k] < 0:
            return None
        for i in range(k + 1, n):
            num = H[i][k] - sum((L[i][j] * L[k][j] * d[j] for j in range(k)), Fraction(0))
            if d[k] == 0:
                if num != 0:
                    return None
            else:
                L[i][k] = num / d[k]
    if any(sum((L[i][k] * d[k] * L[j][k] for k in range(n)), Fraction(0)) != H[i][j]
           for i in range(n) for j in range(n)):
        return None
    return L, d


def _rref_solve(A, b):
    """Some exact solution of A x = b (free variables 0), or None; plus a kernel basis."""
    n = len(A[0])
    rows = [list(r) + [v] for r, v in zip(A, b)]
    pivots = []
    r = 0
    for col in range(n):
        pivot = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        rows[r] = [v / rows[r][col] for v in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [a - f * c for a, c in zip(rows[i], rows[r])]
        pivots.append(col)
        r += 1
    consistent = all(any(v != 0 for v in row[:n]) or row[n] == 0 for row in rows)
    free = [c for c in range(n) if c not in pivots]
    basis = []
    for f in free:
        z = [Fraction(0)] * n
        z[f] = Fraction(1)
        for i, pc in enumerate(pivots):
            z[pc] = -rows[i][f]
        basis.append(z)
    if not consistent:
        return None, basis
    x = [Fraction(0)] * n
    for i, pc in enumerate(pivots):
        x[pc] = rows[i][n]
    return x, basis


def _dot(a, b):
    return sum((u * v for u, v in zip(a, b)), Fraction(0))


def _mul(A, B):
    return [[sum((A[i][k] * B[k][j] for k in range(len(B))), Fraction(0)) for j in range(len(B[0]))]
            for i in range(len(A))]


def _t(rows):
    return [list(r) for r in zip(*rows)]


def _txt(value):
    if type(value) is list:
        return [_txt(v) for v in value]
    return rational_text(value)


def propose_algebra(raw: object) -> dict:
    if type(raw) is not dict or raw.get('format') != REQUEST or raw.get('profile') not in FIELDS:
        raise AppError('ALGEBRA_INPUT', 'rational algebra request requires format and a known profile')
    profile = raw['profile']
    if set(raw) != {'format', 'profile'} | FIELDS[profile]:
        raise AppError('ALGEBRA_INPUT', 'unexpected profile fields')
    out = {'format': RECEIPT, 'request_identity': semantic_identity('rational-algebra-witness', raw),
           'profile': profile}
    if profile == 'seam':
        H = _mat(raw['H'], label='H')
        n = len(H)
        if len(H[0]) != n:
            raise AppError('ALGEBRA_INPUT', 'H must be square')
        p = raw['pivot']
        if type(p) is not int or not 0 <= p < n:
            raise AppError('ALGEBRA_INPUT', 'pivot must index H')
        symmetric = _symmetric(H)
        bad = [[i, j] for i in range(n) for j in range(n) if H[i][j] - H[i][p] - H[p][j] + H[p][p] != 0]
        diag = {H[i][i] for i in range(n)}
        common = symmetric and not bad and len(diag) == 1
        out.update({'H': _txt(H), 'pivot': p, 'symmetric': symmetric, 'seam_violations': bad[:4],
                    'status': ('COMMON_MODE_RANK_AT_MOST_ONE' if common else
                               'SEAM_RANK_AT_MOST_TWO' if symmetric and not bad else 'SEAM_PREMISES_FAIL'),
                    'common_mode': rational_text(next(iter(diag))) if common else None})
    elif profile in ('schur', 'singular'):
        H = _mat(raw['H'], label='H')
        n = len(H)
        if len(H[0]) != n or not _symmetric(H):
            raise AppError('ALGEBRA_INPUT', 'H must be square and symmetric')
        witness = ldl(H)
        if witness is None:
            raise AppError('ALGEBRA_SCOPE', 'H is not positive semidefinite; no exact LDL witness')
        L, d = witness
        out.update({'H': _txt(H), 'psd_witness': {'L': _txt(L), 'd': _txt(d)}})
        if profile == 'schur':
            B = _mat(raw['B'], rows=n, label='B', limit=MAX_N)
            m = len(B[0])
            if m > MAX_M:
                raise AppError('ALGEBRA_INPUT', 'shell dimension too large')
            C = _mat(raw['C'], rows=m, cols=m, label='C', limit=MAX_M)
            ell = exact_ratio(raw['ell'])
            if ell >= 0:
                raise AppError('ALGEBRA_INPUT', 'ell must be negative')
            shifted = [[H[i][j] - (ell if i == j else 0) for j in range(n)] for i in range(n)]
            X = [[Fraction(0)] * m for _ in range(n)]
            for col in range(m):
                sol, _ = _rref_solve(shifted, [B[i][col] for i in range(n)])
                if sol is None:
                    raise AppError('ALGEBRA_INTERNAL', 'shifted matrix must be invertible')
                for i in range(n):
                    X[i][col] = sol[i]
            BtX = _mul(_t(B), X)
            S = [[C[i][j] - (ell if i == j else 0) - BtX[i][j] for j in range(m)] for i in range(m)]
            out.update({'B': _txt(B), 'C': _txt(C), 'ell': rational_text(ell), 'X': _txt(X),
                        'shell_complement': _txt(S), 'status': 'SHELL_COMPLEMENT_IDENTIFIED'})
        else:
            b = _vec(raw['b'], n, 'b')
            c = exact_ratio(raw['c'])
            x, basis = _rref_solve(H, b)
            out.update({'b': _txt(b), 'c': rational_text(c)})
            if x is not None:
                g = c - _dot(b, x)
                out.update({'compatible': True, 'preimage': _txt(x), 'response': rational_text(_dot(b, x)),
                            'gap': rational_text(g), 'kernel_witness': None,
                            'status': 'NONNEGATIVE_BORDERED_FORM' if g >= 0 else 'NEGATIVE_BORDERED_DIRECTION'})
            else:
                z = next(v for v in basis if _dot(b, v) != 0)
                out.update({'compatible': False, 'preimage': None, 'response': None, 'gap': None,
                            'kernel_witness': _txt(z), 'status': 'INCOMPATIBLE_NEGATIVE_DIRECTION'})
    else:
        x = _vec(raw['x'], label='x')
        y = _vec(raw['y'], len(x), 'y')
        c = exact_ratio(raw['c'])
        if c <= 0:
            raise AppError('ALGEBRA_INPUT', 'c must be positive')
        xx, yy, xy = _dot(x, x), _dot(y, y), _dot(x, y)
        gap = xx * yy - xy ** 2
        w = [xx * yi - xy * xi for xi, yi in zip(x, y)]
        positive = gap > 0
        out.update({'x': _txt(x), 'y': _txt(y), 'c': rational_text(c), 'gap': rational_text(gap),
                    'witness': _txt(w), 'signed_value': rational_text(-c * gap ** 2),
                    'threshold': rational_text(c * gap / xx) if positive else None,
                    'status': 'POSITIVE_GAP_SEPARATION' if positive else 'ZERO_GAP_NO_SEPARATION'})
    out.update({'feature_identification': 'NOT_ESTABLISHED_EXPLICIT_PREMISE',
                'lean_status': 'NOT_EXECUTED', 'empirical_identification': 'NOT_IDENTIFIED',
                'scientific_claims_verified': False})
    return out

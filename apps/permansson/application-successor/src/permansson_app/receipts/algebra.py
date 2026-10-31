"""Independent exact checker for rational algebra witness receipts.

Does not import the producer. Re-derives each profile's identities from the
request and validates the stated witnesses: the LDLᵀ factorization with a
nonnegative diagonal, the shifted solve and shell complement, the preimage or
the kernel vector, the Gram gap, witness, signed value and threshold, and the
status logic. It is not a Lean proof or an independent certification.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import exact_ratio,exact_result
from ..identity import canonical_bytes, semantic_identity, rational_text

REQUEST = 'Permansson.App.RationalAlgebraRequest.v1'
RECEIPT = 'Permansson.App.RationalAlgebraReceipt.v1'
COMMON = {'format', 'request_identity', 'profile', 'feature_identification', 'lean_status',
          'empirical_identification', 'scientific_claims_verified', 'status'}
KEYS = {'seam': {'H', 'pivot', 'symmetric', 'seam_violations', 'common_mode'},
        'schur': {'H', 'psd_witness', 'B', 'C', 'ell', 'X', 'shell_complement'},
        'singular': {'H', 'psd_witness', 'b', 'c', 'compatible', 'preimage', 'response', 'gap', 'kernel_witness'},
        'gram': {'x', 'y', 'c', 'gap', 'witness', 'signed_value', 'threshold'}}


def _fail(msg):
    raise AppError('ALGEBRA_RECEIPT', msg)


def _q(v):
    if type(v) is not str:
        _fail('rationals must be strings')
    return exact_result(v)


def _m(rows):
    if type(rows) is not list or any(type(r) is not list for r in rows):
        _fail('bad matrix')
    return [[_q(v) for v in r] for r in rows]


def _v(row):
    if type(row) is not list:
        _fail('bad vector')
    return [_q(v) for v in row]


def _mul(A, B):
    return [[sum((A[i][k] * B[k][j] for k in range(len(B))), Fraction(0)) for j in range(len(B[0]))]
            for i in range(len(A))]


def _dot(a, b):
    return sum((u * v for u, v in zip(a, b)), Fraction(0))


def _psd(H, witness):
    if type(witness) is not dict or set(witness) != {'L', 'd'}:
        _fail('bad PSD witness')
    L, d = _m(witness['L']), _v(witness['d'])
    n = len(H)
    if len(L) != n or len(d) != n or any(v < 0 for v in d):
        _fail('PSD witness has a negative pivot')
    D = [[d[i] if i == j else Fraction(0) for j in range(n)] for i in range(n)]
    if _mul(_mul(L, D), [list(r) for r in zip(*L)]) != H:
        _fail('LDL witness does not reproduce H')


def check_algebra(raw: object, receipt: object) -> dict:
    if type(raw) is not dict or raw.get('format') != REQUEST or type(receipt) is not dict:
        _fail('unsupported request or receipt')
    profile = raw.get('profile')
    if profile not in KEYS or receipt.get('profile') != profile or set(receipt) != COMMON | KEYS[profile]:
        _fail('profile fields mismatch')
    if (receipt['format'] != RECEIPT or receipt['lean_status'] != 'NOT_EXECUTED'
            or receipt['scientific_claims_verified'] is not False
            or receipt['empirical_identification'] != 'NOT_IDENTIFIED'
            or receipt['feature_identification'] != 'NOT_ESTABLISHED_EXPLICIT_PREMISE'
            or receipt['request_identity'] != semantic_identity('rational-algebra-witness', raw)):
        _fail('false scope or identity')
    if profile == 'seam':
        H = [[exact_ratio(v) for v in r] for r in raw['H']]
        n, p = len(H), raw['pivot']
        if _m(receipt['H']) != H or receipt['pivot'] != p:
            _fail('input mismatch')
        sym = all(H[i][j] == H[j][i] for i in range(n) for j in range(n))
        bad = [[i, j] for i in range(n) for j in range(n) if H[i][j] - H[i][p] - H[p][j] + H[p][p] != 0]
        common = sym and not bad and len({H[i][i] for i in range(n)}) == 1
        expected = ('COMMON_MODE_RANK_AT_MOST_ONE' if common else
                    'SEAM_RANK_AT_MOST_TWO' if sym and not bad else 'SEAM_PREMISES_FAIL')
        if (receipt['symmetric'] is not sym or receipt['seam_violations'] != bad[:4]
                or receipt['status'] != expected
                or receipt['common_mode'] != (rational_text(H[0][0]) if common else None)):
            _fail('seam status mismatch')
    elif profile in ('schur', 'singular'):
        H = [[exact_ratio(v) for v in r] for r in raw['H']]
        if _m(receipt['H']) != H:
            _fail('input mismatch')
        _psd(H, receipt['psd_witness'])
        n = len(H)
        if profile == 'schur':
            B = [[exact_ratio(v) for v in r] for r in raw['B']]
            C = [[exact_ratio(v) for v in r] for r in raw['C']]
            ell = exact_ratio(raw['ell'])
            X, S = _m(receipt['X']), _m(receipt['shell_complement'])
            m = len(C)
            if _m(receipt['B']) != B or _m(receipt['C']) != C or _q(receipt['ell']) != ell or ell >= 0:
                _fail('input mismatch')
            shifted = [[H[i][j] - (ell if i == j else 0) for j in range(n)] for i in range(n)]
            if _mul(shifted, X) != B:
                _fail('X does not solve the shifted system')
            BtX = _mul([list(r) for r in zip(*B)], X)
            if S != [[C[i][j] - (ell if i == j else 0) - BtX[i][j] for j in range(m)] for i in range(m)]:
                _fail('shell complement mismatch')
            if receipt['status'] != 'SHELL_COMPLEMENT_IDENTIFIED':
                _fail('status mismatch')
        else:
            b = [exact_ratio(v) for v in raw['b']]
            c = exact_ratio(raw['c'])
            if _v(receipt['b']) != b or _q(receipt['c']) != c:
                _fail('input mismatch')
            if receipt['compatible'] is True:
                x = _v(receipt['preimage'])
                if [_dot(r, x) for r in H] != b:
                    _fail('preimage does not map to b')
                if _q(receipt['response']) != _dot(b, x) or _q(receipt['gap']) != c - _dot(b, x):
                    _fail('response or gap mismatch')
                if receipt['kernel_witness'] is not None or receipt['status'] != (
                        'NONNEGATIVE_BORDERED_FORM' if c - _dot(b, x) >= 0 else 'NEGATIVE_BORDERED_DIRECTION'):
                    _fail('status mismatch')
            elif receipt['compatible'] is False:
                z = _v(receipt['kernel_witness'])
                if any(_dot(r, z) != 0 for r in H) or _dot(b, z) == 0:
                    _fail('kernel witness is invalid')
                if (receipt['preimage'], receipt['response'], receipt['gap']) != (None, None, None) or \
                        receipt['status'] != 'INCOMPATIBLE_NEGATIVE_DIRECTION':
                    _fail('status mismatch')
            else:
                _fail('compatible must be boolean')
    else:
        x, y = [exact_ratio(v) for v in raw['x']], [exact_ratio(v) for v in raw['y']]
        c = exact_ratio(raw['c'])
        if _v(receipt['x']) != x or _v(receipt['y']) != y or _q(receipt['c']) != c or c <= 0:
            _fail('input mismatch')
        xx, yy, xy = _dot(x, x), _dot(y, y), _dot(x, y)
        gap = xx * yy - xy ** 2
        if _q(receipt['gap']) != gap or _v(receipt['witness']) != [xx * b - xy * a for a, b in zip(x, y)]:
            _fail('gap or witness mismatch')
        if _q(receipt['signed_value']) != -c * gap ** 2:
            _fail('signed value mismatch')
        positive = gap > 0
        if receipt['threshold'] != (rational_text(c * gap / xx) if positive else None) or \
                receipt['status'] != ('POSITIVE_GAP_SEPARATION' if positive else 'ZERO_GAP_NO_SEPARATION'):
            _fail('threshold or status mismatch')
    return {'format': 'Permansson.App.IndependentAlgebraCheck.v1', 'status': 'PASS', 'profile': profile,
            'witness_status': receipt['status'],
            'receipt_sha256': sha256(canonical_bytes(receipt)).hexdigest(),
            'lean_status': 'NOT_EXECUTED', 'scientific_claims_verified': False}

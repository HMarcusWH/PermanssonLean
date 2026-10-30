# Semantic and execution digests — `Permansson.App.SemanticsJCS.v1`

**Development scope:** APP-07/APP-08, `feature/application-successor-full`,
PR #115. A new, versioned identity profile. Nothing that already exists is
recomputed: `identity.semantic_identity` (`TypedRationalJCS.v1`), raw
artifact SHA-256 values, prototype/native canonical hashes and pipeline
digests keep their exact bytes.

## Definitions (`permansson_app.digest`)

```
canonical_semantics(v) = RFC8785(v)            # restricted value profile
semantic_digest(v)     = SHA256("PERMANSSON_APP_SEMANTICS_JCS_V1" || 0x00 || canonical_semantics(v))
execution_digest(e)    = SHA256("PERMANSSON_APP_EXECUTION_JCS_V1" || 0x00 || canonical_semantics(e))
```

`e` has exactly the fields `semantic_digest`, `wrapper`, `registry`,
`provider`, `runtime`, `mode` and `resource_profile`.

Values must already be normalized by their owning schema: reduced rational
strings (`rational_text`), integers with |n| ≤ 2^53 − 1, Unicode scalar
strings without implicit normalization, string keys and explicit arrays
(array order is semantic). Floats, non-finite constants, unsafe integers,
lone surrogates, non-string keys, `Fraction` and set objects are rejected
with structured `AppError`s. Full RFC 8785 number support is **not** claimed.

## Implementation and oracles

Encoding uses the pinned `rfc8785==0.1.4` (`dumps`), an optional `semantics`
extra rather than a mandatory runtime dependency while no runtime path
advertises this profile. It is hash-pinned in `requirements-runtime.lock`;
a missing canonicalizer raises `DIGEST_DEPENDENCY_MISSING`. Every encoding
must also equal the bytes of the independent restricted encoder in
`identity`; any disagreement raises `DIGEST_IMPLEMENTATION_DISAGREEMENT` and
no digest is issued — there is no fallback to `json.dumps`.

`tests/test_digest.py` checks:

- the official JCS vectors from `cyberphone/json-canonicalization`
  (commit `32a48195b9b20fe67b1795e39e4509f14d860b45`, Apache-2.0), vendored
  byte-for-byte in `tests/fixtures/rfc8785_official` with SHA-256 provenance:
  the pinned library reproduces all six, the restricted profile reproduces
  the four float-free ones and rejects the two with floats;
- UTF-16 key order that differs from code-point order, escapes and literals
  against hand-written bytes;
- raw-whitespace changes alter raw hashes but not semantics; rationals are
  normalized before encoding, never implicitly; meaningful changes of mode,
  α, comparison order, information structure and nature order alter the
  digest; domain separation from plain SHA-256 and between the two tags;
- `tests/fixtures/semantic_digest_vectors.json`: published canonical hex,
  SHA-256 and semantic digest for application-shaped values plus reject
  cases, each re-derived by both encoders and `hashlib`.

The profile is available to callers; no existing receipt, report or bundle
identity has been switched to it.

## Locked environments

`requirements-runtime.lock`, `requirements-test.lock` (which includes the
runtime lock) and `requirements-build.lock` list PyPI's published SHA-256
digest of every file of each exact pinned version, resolved for CPython 3.13
(3.12 adds the marked `typing-extensions` pin). The Research-route source
suite installs `requirements-test.lock` with `--require-hashes` when its
interpreter lacks the dependencies; the installed-distribution test builds
with `--no-isolation` from `requirements-build.lock`, installs
`requirements-test.lock` with `--require-hashes`, installs the wheel with
`--no-deps` and runs `pip check`.

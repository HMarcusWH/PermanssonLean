# PR113 selection candidate survey (P1-06 / P1-08)

**Status: UNREVIEWED tooling. This survey is not a selection, a review or an
acceptance.** It lists the choices a nonauthor reviewer must still make before
`reviewed_positive45_selection_v31.json` and `reviewed_claim11_selection_v31.json`
(plus the eleven claim false sources) can exist. It never writes those files.

## Command

From a clean checkout of the exact head being surveyed:

```sh
PYTHONPATH=.:verification/research python3 -B \
  verification/research/pr113_selection_candidate_survey.py \
  --head "$(git rev-parse HEAD)" \
  --out /path/outside/the/checkout/pr113-selection-survey
```

- Reads only the committed exact-H blobs of
  `research/paper_closures/post_merge_112/acceptance_case_source_map.json`,
  `claim_declaration_map.json` and the test/Lean sources they name
  (`git cat-file`, not the working tree).
- Writes `selection_candidate_survey.json` and `selection_candidate_survey.md`
  into a new directory outside the checkout. A directory named `reviewed_*` is
  refused.
- Exit `0`: coverage complete. Exit `1`: report written, but some case/claim
  has no eligible route, provider or two test methods. Exit `2`: blocked.
  Malformed maps, missing, duplicate or foreign owners, provider paths outside
  `PermanssonLean/`/`PermanssonResearch/`, foreign test paths, unknown route
  roles and unparseable test sources all block, and nothing is written.
- Output is deterministic: two runs at the same head are byte-identical.

A positive route is `ELIGIBLE_UNREVIEWED` only when its role is
`COMPILER_SOURCE`/`EXACT_CHECK`, its test file exists at H and AST inspection
finds the method in exactly one class. Otherwise it is `ABSENT_TEST_SOURCE`,
`ABSENT_METHOD` or `AMBIGUOUS_CLASS`. Eligibility is a well-formedness fact
only. Whether the method tests the original criterion is the reviewer's
decision.

Tests: `PYTHONPATH=.:verification/research python3 -B -m unittest test_pr113_selection_candidate_survey`.

## Findings at `1ae74fc130c8e44fc3534e44c1d1dac1cefbf0a7`

Coverage is complete: 45/45 cases have at least one eligible positive route
and a Lean provider present at H. 11/11 claims have a provider and at least
two discovered test methods. None of this is review.

## Reviewer decisions still open

**Original cases (P1-06).**

1. **Choose one positive route** for each of the 16 cases with several
   eligible routes: A-01, B-02, D-01, D-03, D-04, D-07, D-09, E-05, F-01,
   F-03, M-01, M-02, Q-03, Q-04, Q-05, X-03 (Q-05 has five, D-09 three).
2. **Choose the Lean provider** for the 33 cases declaring more than one
   provider file. The JSON `summary.cases_with_multiple_lean_providers` lists
   them.
3. **Confirm criterion relevance** of the chosen route for all 45 cases,
   including the 29 with a single eligible route.
4. **Pick the relevant semantic negative** (P1-07) where several exist:
   B-02, M-02, Q-05, X-02, X-05.

**Claims (P1-08).**

5. **Choose distinct positive and negative test class/method** for all 11
   claims. The claim map names test files only, not methods.
6. **Keep tests claim-specific.** M1/M2 share `test_final05_measurable_lean.py`
   and Q1/Q2 share `test_final04_source_lean.py`, each file having only two
   test methods, so one claim must not borrow the other's controls.
7. **Choose the provider** for N1 and N2, which have two provider files each.
8. **Author a false Lean statement for each claim.** It must be
   claim-specific, criterion-relevant and append-only to the chosen provider,
   with no import, axiom, option or `sorry` change. The survey deliberately
   provides none (`negative_lean_statement: null`).

## Boundaries

This tool does not modify canonical maps, Lean sources, workflows, manifests,
release gates or reviewer policy. It sets no accepted/approved flag, and every
report carries `independent_review: false`, `accepted_cases: 0` and
`accepted_claims: 0`. The reviewed selection files stay absent until a
configured nonauthor reviewer (P1-19) produces them.

"""Revalidate actual v3.1 control execution bytes inside authenticated GH ZIPs.

This validates retained bytes and diagnostic kinds, NOT mathematical
relevance, historical security approval, reviewer authority, or release.
Call only after final_closure_extra_producers_v31 authenticates the actual
run, job, check, workflow Git blob and original GitHub artifact digest.

The full validator also binds every positive and claim owner to its exact-H
canonical route (case/claim map, committed test and Lean source bytes,
named class/method and its own `unittest -v` line).  An optional reviewed
selection is compared exactly; route binding is NOT relevance review.
"""
from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

from final_closure_producer_bytes import inspect_zip, ProducerBytesError

SHA256 = re.compile(r"^[0-9a-f]{64}$")
CLAIMS = frozenset(("Q1", "Q2", "Q3", "M1", "M2", "M3",
                    "N1", "N2", "N3", "D8", "D9"))
STATUSES = {
    "original_positive": "SOURCE_TEST_AND_LEAN_EXECUTED_UNREVIEWED",
    "legacy_negative": "SOURCE_APPENDED_REPLAYED_UNREVIEWED_NOT_CI_ATTRIBUTED",
    "claim_pair": "LEAN_POSITIVE_AND_FALSE_MUTANT_EXECUTED_UNREVIEWED",
}
REQUIRED_CLAIM_MEMBERS = frozenset((
    "original.lean", "appended_false.lean",
    "positive_lean.log", "negative_lean.log",
    "positive_test.stdout", "positive_test.stderr",
    "negative_test.stdout", "negative_test.stderr",
))
POSITIVE_FORMAT = "Permansson.PR113.OriginalCasePositiveCandidate.v1"
POSITIVE_ROLES = ("COMPILER_SOURCE", "EXACT_CHECK")
TEST_PATH = re.compile(r"^verification/research/test_[A-Za-z0-9_]+\.py$")
LEAN_PATH = re.compile(r"^Permansson(?:Lean|Research)/[A-Za-z0-9_/]+\.lean$")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
TEST_METHOD = re.compile(r"^test_[A-Za-z0-9_]+$")
CASE_MAP = "research/paper_closures/post_merge_112/acceptance_case_source_map.json"
CLAIM_MAP = "research/paper_closures/post_merge_112/claim_declaration_map.json"
POSITIVE_SELECTION = "Permansson.PR113.OriginalPositiveSelection.v1"
CLAIM_SELECTION_KEYS = frozenset((
    "claim_id", "proof_source_path", "positive_test_path",
    "positive_test_class", "positive_test_method",
    "negative_test_path", "negative_test_class", "negative_test_method",
))


class RealControlError(ValueError):
    pass


class ExactSource:
    """Canonical exact-H routes plus a committed-blob reader (read-only).

    `blob(path)` must return the committed Git blob of `path` at `head`.
    Selections, when given, are reviewed external inputs keyed by owner ID;
    their absence is reported, never treated as relevance review.
    """

    def __init__(self, head, case_map, claim_map, blob, *,
                 positive_selection=None, claim_selection=None):
        cases = case_map.get("cases") if isinstance(case_map, dict) else None
        claims = claim_map.get("claims") if isinstance(claim_map, dict) else None
        need(isinstance(head, str) and re.fullmatch(r"[0-9a-f]{40}", head) and
             isinstance(cases, list) and isinstance(claims, list) and
             callable(blob), "exact-H canonical route source unavailable")
        self.head = head
        self.cases = {row.get("case_id"): row for row in cases
                      if isinstance(row, dict)}
        self.claims = {row.get("claim_id"): row for row in claims
                       if isinstance(row, dict)}
        need(len(self.cases) == len(cases) and
             len(self.claims) == len(claims),
             "canonical case/claim route identities are not unique")
        self._blob = blob
        self._cache = {}
        self.positive_selection = self._positive(positive_selection)
        self.claim_selection = self._claims(claim_selection)

    def _positive(self, payload):
        if payload is None:
            return None
        need(isinstance(payload, dict) and
             payload.get("format") == POSITIVE_SELECTION and
             isinstance(payload.get("cases"), list),
             "reviewed positive selection is malformed")
        rows = {}
        for row in payload["cases"]:
            need(isinstance(row, dict) and row.get("case_id") in self.cases and
                 row["case_id"] not in rows,
                 "reviewed positive selection names a foreign/duplicate case")
            rows[row["case_id"]] = row
        return rows

    def _claims(self, payload):
        if payload is None:
            return None
        need(isinstance(payload, dict) and
             isinstance(payload.get("claims"), list),
             "reviewed claim selection is malformed")
        rows = {}
        for row in payload["claims"]:
            need(isinstance(row, dict) and set(row) == CLAIM_SELECTION_KEYS and
                 row["claim_id"] in self.claims and row["claim_id"] not in rows,
                 "reviewed claim selection names a foreign/duplicate claim")
            rows[row["claim_id"]] = row
        return rows

    def blob(self, path):
        need(isinstance(path, str) and path and
             not PurePosixPath(path).is_absolute() and
             ".." not in PurePosixPath(path).parts and ":" not in path,
             "unsafe canonical source path")
        if path not in self._cache:
            raw = self._blob(path)
            need(type(raw) is bytes, "exact-H committed source unavailable: " +
                 path)
            self._cache[path] = raw
        return self._cache[path]


def git_blob_reader(head, root):
    """Read committed blobs of exact H without trusting the working tree."""
    def read(path):
        try:
            result = subprocess.run(
                ["git", "cat-file", "blob", head + ":" + path],
                cwd=root, capture_output=True, timeout=30)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise RealControlError("committed exact-H source unavailable") from exc
        need(result.returncode == 0,
             "source not tracked at exact H: " + path)
        return result.stdout
    return read


def exact_source(head, root=None, *, positive_selection=None,
                 claim_selection=None):
    root = Path(root) if root is not None else Path(__file__).resolve().parents[2]
    read = git_blob_reader(head, root)
    return ExactSource(head, json_bytes(read(CASE_MAP)),
                       json_bytes(read(CLAIM_MAP)), read,
                       positive_selection=positive_selection,
                       claim_selection=claim_selection)


def need(ok, message):
    if not ok:
        raise RealControlError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def json_bytes(raw):
    need(type(raw) is bytes and len(raw) <= 4 * 1024 * 1024,
         "unbounded or missing source control JSON")
    try:
        return json.loads(raw)
    except (ValueError, UnicodeError, TypeError) as exc:
        raise RealControlError("original control receipt is invalid JSON") from exc


def member(members, name, expected):
    need(isinstance(name, str) and name and
         name in members and
         type(members[name]) is bytes and
         len(members[name]) <= 4 * 1024 * 1024 and
         isinstance(expected, str) and SHA256.fullmatch(expected) and
         sha(members[name]) == expected,
         "original producer member not present at authenticated digest: " +
         str(name))
    return members[name]


def source_clean_negative(log):
    text = log.decode("utf-8", errors="replace").lower()
    need("error:" in text and
         any(kind in text for kind in
             ("type mismatch", "unsolved goals", "application type mismatch")),
         "Lean did not reject the intended mathematical proof goal")
    need(not any(kind in text for kind in (
        "unknown module", "unknown identifier", "failed to import",
        "parser error", "syntax error", "out of memory", "timed out",
        "timeout", "maximum number of heartbeats",
        "failed to synthesize", "sorryax", "unknown tactic",
    )), "Lean failed for tooling/parser/resource rather than mathematics")


def defines_method(raw, cls, method):
    try:
        tree = ast.parse(raw.decode("utf-8"))
    except (ValueError, UnicodeError, SyntaxError) as exc:
        raise RealControlError("exact-H test source is not parseable") from exc
    found = [node for node in tree.body
             if isinstance(node, ast.ClassDef) and node.name == cls and
             sum(isinstance(inner, (ast.FunctionDef, ast.AsyncFunctionDef))
                 and inner.name == method for inner in node.body) == 1]
    return len(found) == 1


def ran_exactly(stderr, test_path, method, cls=None):
    """Return the class of the one named `unittest -v` method that passed."""
    text = stderr.decode("utf-8", errors="replace")
    module = re.escape(PurePosixPath(test_path).stem)
    name = re.escape(method)
    klass = re.escape(cls) if cls is not None else r"[A-Za-z_][A-Za-z0-9_]*"
    found = re.findall(
        r"(?m)^" + name + r" \(" + module + r"\.(" + klass + r")(?:\." +
        name + r")?\)(?:\n[^\n]*)? \.\.\. ok$", text)
    need(len(found) == 1 and
         len(re.findall(r"(?m)^Ran 1 test in ", text)) == 1 and
         re.search(r"(?m)^OK$", text) and "FAILED (" not in text,
         "registered test log is not the exact named passing method")
    return found[0]


def bind_positive(source, owner_id, wrapper):
    need(source is not None, "exact-H canonical route source required")
    case = source.cases.get(owner_id)
    need(isinstance(case, dict), "positive owner is not an original case")
    path, cls = wrapper.get("test_path"), wrapper.get("test_class")
    method, proof = wrapper.get("test_name"), wrapper.get("proof_source_path")
    need(wrapper.get("format") == POSITIVE_FORMAT and
         isinstance(path, str) and TEST_PATH.fullmatch(path) and
         isinstance(cls, str) and IDENT.fullmatch(cls) and
         isinstance(method, str) and TEST_METHOD.fullmatch(method) and
         isinstance(proof, str) and LEAN_PATH.fullmatch(proof),
         "positive owner route identity is missing or malformed")
    routes = [r for r in case.get("test_method_candidates", ())
              if isinstance(r, dict) and r.get("path") == path and
              r.get("method") == method and r.get("role") in POSITIVE_ROLES]
    need(len(routes) == 1 and routes[0]["role"] == wrapper.get("positive_role"),
         "positive test is not this case's frozen positive route")
    need(any(isinstance(d, dict) and d.get("path") == proof
             for d in case.get("historical_proof_declarations", ())),
         "positive Lean provider is foreign to the original case")
    test_bytes, proof_bytes = source.blob(path), source.blob(proof)
    need(wrapper.get("source_sha256") == sha(test_bytes) and
         wrapper.get("proof_source_sha256") == sha(proof_bytes),
         "positive test/Lean source digest differs from exact H")
    need(defines_method(test_bytes, cls, method),
         "selected positive class/method is not defined at exact H")
    if source.positive_selection is not None:
        need(source.positive_selection.get(owner_id) == {
                 "case_id": owner_id, "test_path": path, "test_class": cls,
                 "test_method": method, "proof_source_path": proof},
             "positive owner differs from the reviewed route selection")


def bind_claim(source, owner_id, wrapper, content):
    need(source is not None, "exact-H canonical route source required")
    claim = source.claims.get(owner_id)
    need(isinstance(claim, dict), "claim owner is not a mapped new claim")
    original = wrapper.get("original_lean_source_path")
    tests = {
        side: (wrapper.get(side + "_test_path"),
               wrapper.get(side + "_test_name"))
        for side in ("positive", "negative")
    }
    digests = wrapper.get("source_test_hashes")
    need(isinstance(original, str) and LEAN_PATH.fullmatch(original) and
         any(isinstance(d, dict) and d.get("path") == original
             for d in claim.get("declarations", ())),
         "claim Lean provider is foreign to the mapped claim")
    need(content["original.lean"] == source.blob(original),
         "claim original Lean bytes differ from exact H")
    need(isinstance(digests, dict) and set(digests) == set(tests) and
         tests["positive"][1] != tests["negative"][1],
         "claim test identities are incomplete or reused")
    classes = {}
    for side, (path, method) in tests.items():
        need(isinstance(path, str) and TEST_PATH.fullmatch(path) and
             path in claim.get("test_source_candidates", ()) and
             isinstance(method, str) and TEST_METHOD.fullmatch(method),
             "claim test is not a mapped source candidate")
        raw = source.blob(path)
        need(digests[side] == sha(raw),
             "claim test source digest differs from exact H")
        cls = ran_exactly(content[side + "_test.stderr"], path, method)
        need(defines_method(raw, cls, method),
             "claim test class/method is not defined at exact H")
        classes[side] = cls
    if source.claim_selection is not None:
        need(source.claim_selection.get(owner_id) == {
                 "claim_id": owner_id, "proof_source_path": original,
                 "positive_test_path": tests["positive"][0],
                 "positive_test_class": classes["positive"],
                 "positive_test_method": tests["positive"][1],
                 "negative_test_path": tests["negative"][0],
                 "negative_test_class": classes["negative"],
                 "negative_test_method": tests["negative"][1]},
             "claim owner differs from the reviewed claim selection")


def verify_owner(kind, owner_id, receipt_name, members, head, source=None, original_producers=None):
    """Return an unreviewed byte-evidence diagnostic or fail closed.

    Without `source` only retained bytes are checked (producer-side packing);
    the final authenticator always passes the exact-H ExactSource.
    """
    need(kind in STATUSES and isinstance(owner_id, str) and owner_id and
         isinstance(receipt_name, str) and receipt_name.endswith(".json") and
         receipt_name in members,
         "missing typed original control owner")
    wrapper = json_bytes(members[receipt_name])
    owner_key = "claim_id" if kind == "claim_pair" else "case_id"
    need(wrapper.get("status") == STATUSES[kind] and
         wrapper.get("head_sha") == head and
         wrapper.get(owner_key) == owner_id and
         wrapper.get("scientific_release_approved") is False,
         "source execution owner falsely promoted or mismatched")
    base = receipt_name.rsplit("/", 1)[0] + "/"
    if kind == "original_positive":
        need(wrapper.get("positive_role") in ("COMPILER_SOURCE", "EXACT_CHECK") and
             type(wrapper.get("source_positive_exit_code")) is int and
             wrapper["source_positive_exit_code"] == 0 and
             type(wrapper.get("registered_method_exit_code")) is int and
             wrapper["registered_method_exit_code"] == 0 and
             wrapper.get("actual_producing_check_run_id") is None and
             wrapper.get("authenticated_ci_artifact") is False and
             wrapper.get("independent_case_review") is False,
             "invalid original positive control execution")
        logs = (
            ("unittest_stdout.log", "unittest_stdout_sha256"),
            ("unittest_stderr.log", "unittest_stderr_sha256"),
            ("source_positive.log", "source_positive_log_sha256"),
        )
        raw = {}
        for name, digest_field in logs:
            raw[name] = member(members, base + name, wrapper.get(digest_field))
        test = raw["unittest_stderr.log"].decode("utf-8", errors="replace")
        compiled = raw["source_positive.log"].decode("utf-8", errors="replace").lower()
        need("Ran 1 test" in test and "OK" in test and
             "skipped=" not in test and "FAILED (" not in test and
             "error:" not in compiled and "sorryax" not in compiled,
             "registered true control or Lean source did not pass")
        if source is not None:
            bind_positive(source, owner_id, wrapper)
            ran_exactly(raw["unittest_stderr.log"], wrapper["test_path"],
                        wrapper["test_name"], wrapper["test_class"])
        return {"kind": kind, "owner_id": owner_id,
                "actual_log_members_checked": 3}

    if kind == "claim_pair":
        need(owner_id in CLAIMS and
             wrapper.get("format") == "Permansson.PR113.ClaimOnlyControlCandidate.v1" and
             wrapper.get("claim_ids") == [owner_id] and
             wrapper.get("case_ids") == [] and
             type(wrapper.get("lean_positive_exit_code")) is int and
             wrapper.get("lean_positive_exit_code") == 0 and
             type(wrapper.get("lean_negative_exit_code")) is int and
             wrapper["lean_negative_exit_code"] != 0 and
             wrapper.get("actual_ci_check_run_id") is None and
             wrapper.get("independent_mathematical_review") is False and
             wrapper.get("accepted_claim") is False,
             "claim positive/negative paths are missing or self-approved")
        hashes = wrapper.get("retained_member_sha256")
        need(isinstance(hashes, dict) and set(hashes) == REQUIRED_CLAIM_MEMBERS,
             "claim proof source/log set is incomplete")
        content = {
            name: member(members, base + name, hashes[name])
            for name in REQUIRED_CLAIM_MEMBERS
        }
        original = content["original.lean"]
        false = content["appended_false.lean"]
        need(len(original) > 0 and false.startswith(original) and
             len(false) > len(original), "claim false proof was not append-only")
        append = false[len(original):].decode("utf-8", errors="strict")
        need(not re.search(
                 r"(?mi)^\s*(?:import|axiom|constant|opaque|set_option)\b",
                 append) and
             not re.search(r"(?i)\b(?:sorry|sorryAx|admit)\b", append),
             "claim mutant silently changed its proof assumptions")
        source_clean_negative(content["negative_lean.log"])
        pl = content["positive_lean.log"].decode("utf-8", errors="replace").lower()
        need("error:" not in pl and "sorryax" not in pl and
             "ok" in content["positive_test.stderr"].decode(
                 "utf-8", errors="replace").lower() and
             "ok" in content["negative_test.stderr"].decode(
                 "utf-8", errors="replace").lower(),
             "claim source positive / registered test failed")
        if source is not None:
            bind_claim(source, owner_id, wrapper, content)
        return {"kind": kind, "owner_id": owner_id,
                "actual_log_members_checked": len(content)}

    need(wrapper.get("independent_case_review") is False and
         wrapper.get("actual_ci_check_run_id") is None and
         wrapper.get("mathematical_acceptance") is False and
         type(wrapper.get("historical_producing_artifact_id")) is int and
         wrapper["historical_producing_artifact_id"] > 0,
         "historical source-negative owner fabricated current CI acceptance")
    replay_raw = member(
        members, wrapper.get("execution_receipt_member"),
        wrapper.get("execution_receipt_sha256"))
    replay = json_bytes(replay_raw)
    raw_zip = members.get(wrapper.get("semantic_zip_member"))
    need(type(raw_zip) is bytes and
         len(raw_zip) <= 64 * 1024 * 1024 and
         sha(raw_zip) == wrapper.get("semantic_zip_sha256"),
         "historical original source-appended replay ZIP missing or modified")
    try:
        nested = inspect_zip(raw_zip)
    except ProducerBytesError as exc:
        raise RealControlError("unsafe historical nested compiler ZIP") from exc
    mut = replay.get("mutation_record")
    need(replay.get("format") ==
            "Permansson.LegacyAppendOnlyReplayCandidate.v1" and
         replay.get("status") ==
            "REPLAYED_APPEND_ONLY_UNREVIEWED_UNATTRIBUTED" and
         replay.get("case_id") == owner_id and
         replay.get("head_sha") == head and
         replay.get("independent_review") is False and
         replay.get("mathematical_acceptance") is False and
         replay.get("ci_check_run_id") is None and
         isinstance(mut, dict) and
         mut.get("head_sha") == head and
         mut.get("case_ids") == [owner_id] and
         mut.get("outcome") == "REJECTED_SEMANTIC" and
         type(mut.get("compiler_exit_code")) is int and
         mut["compiler_exit_code"] != 0 and
         isinstance(mut.get("positive_control"), dict) and
         mut["positive_control"].get("compiled") is True and
         mut["positive_control"].get("exit_code") == 0,
         "historical replay did not actually execute source positive and false")
    pos = mut["positive_control"]
    poslog = member(nested, pos.get("log_member"), pos.get("log_sha256"))
    neglog = member(nested, mut.get("log_member"), mut.get("log_sha256"))
    original = member(nested, mut.get("original_lean_source_member"),
                      mut.get("original_lean_source_sha256"))
    false = member(nested, mut.get("mutant_source_member"),
                   mut.get("mutant_source_sha256"))
    need(false.startswith(original) and len(false) > len(original),
         "legacy false assertion did not retain full original Lean provider")
    need("error:" not in poslog.decode("utf-8", errors="replace").lower(),
         "historical original positive control did not compile")
    source_clean_negative(neglog)
    if source is not None:
        from pr113_legacy_route_binding import bind_legacy, LegacyRouteError
        try:
            bind_legacy(
                head, owner_id, replay, mut, wrapper,
                original, false, source=source,
                authenticated_original=original_producers)
        except LegacyRouteError as exc:
            raise RealControlError(
                "original legacy case/provider/observation route mismatch: " +
                str(exc)) from exc
    return {"kind": kind, "owner_id": owner_id,
            "actual_log_members_checked": 4}


def validate_executed_controls(head, contract, zipped, *, source, original_producers=None):
    """Validate all 76 original GH ZIP owner payloads, without review claims."""
    need(isinstance(contract, dict) and contract.get("head_sha") == head and
         isinstance(zipped, dict), "original v3.1 CI payload unavailable")
    need(isinstance(source, ExactSource) and source.head == head,
         "exact-H canonical route source required for 76-owner binding")
    need(isinstance(original_producers, dict) and
         original_producers.get("status") ==
             "REAL_PRODUCING_BYTES_UNREVIEWED" and
         original_producers.get("head_sha") == head and
         original_producers.get("producer_count") == 21,
         "all 21 authenticated original producers required for legacy capture linkage")
    owners = {}
    jobs = contract.get("producers")
    need(isinstance(jobs, list) and jobs and
         {j.get("artifact_id") for j in jobs} == set(zipped),
         "producer artifacts not in exact declared set")
    for job in jobs:
        raw = zipped[job["artifact_id"]]
        need(type(raw) is bytes, "missing genuine original ZIP bytes")
        try:
            members = inspect_zip(raw)
        except ProducerBytesError as exc:
            raise RealControlError("unsafe original source producer ZIP") from exc
        for row in job["owners"]:
            key = (row["kind"], row["owner_id"])
            need(key not in owners, "duplicate source control owner")
            name = row["receipt_member"]
            member(members, name, row["receipt_sha256"])
            owners[key] = verify_owner(
                row["kind"], row["owner_id"], name, members, head,
                source, original_producers)
    from collections import Counter
    n = Counter(kind for kind, _ in owners)
    need(len(owners) == 76 and n == {
         "original_positive": 45, "legacy_negative": 20, "claim_pair": 11
    }, "original complete 45/20/11 source-control ownership incomplete")
    need({k[1] for k in owners if k[0] == "claim_pair"} == CLAIMS,
         "claim owner identity differs from original eleven")
    return {
        "format": "Permansson.PR113.GenuineSourceExecutionBytes.v1",
        "status": "ACTUAL_CONTROL_BYTES_REVALIDATED_UNREVIEWED",
        "source_head": head,
        "source_owner_count": 76,
        "claim_positive_negative_directions": 22,
        "execution_log_members_checked": sum(
            row["actual_log_members_checked"] for row in owners.values()),
        "canonical_routes_bound": True,
        "legacy_original_captures_bound": True,
        "reviewed_positive_selection_bound":
            source.positive_selection is not None,
        "reviewed_claim_selection_bound": source.claim_selection is not None,
        "independent_review": False,
        "mathematical_acceptance": False,
        "publication_approved": False,
    }

"""Exact 25-history / 30-successor workflow candidate, without activation authority.

Read all workflow bytes from Git objects. The historical 25-workflow preactivation
snapshot is a real, immutable ancestor, NOT the 19-workflow #113 original base.
This checker does not install files, authorize an action tag, or accept CI.
"""
from __future__ import annotations

import hashlib
from contextlib import contextmanager
import importlib.machinery
import importlib.util
import json
from pathlib import Path
import re
import sys

import archive_successor_approval_v1 as approval
from pr113_boundary_io import strict_json_object
from pr113_tooling_migration import (
    ROOT, git, exact_tree, require, ToolingMigrationError,
)

FORMAT = "Permansson.PR113.VersionedWorkflowEvidence.v2"
PREACTIVATION_HEAD = "5189f0c4a0db7535d57a9ff2a7aef6a3e76191b6"
STAGE = "docs/operations/pr113_required_gate_replacement_unapproved/"
PROPOSALS = "docs/operations/pr113_unapproved_workflows/"
CONTRACT = STAGE + "workflow_contract_v2.py"
CONTRACT_MANIFEST = STAGE + "workflow_contract_v2_manifest.json"
FULL_MANIFEST = STAGE + "full_workflow_manifest.json"
PROPOSAL_MANIFEST = PROPOSALS + "manifest.json"
SHA = re.compile(r"^[a-f0-9]{40}$")


def _check_import_origin(name, helper_root):
    """Reject cached package parents that could redirect the staged import."""
    if name not in sys.modules:
        return
    module = sys.modules[name]
    expected = helper_root.joinpath(*name.split("."))
    require(module is not None, "versioned contract import is unavailable: " + name)
    if name == "verification":
        require(getattr(module, "__file__", None) is None
                and {Path(p).resolve() for p in getattr(module, "__path__", ())}
                    == {expected},
                "versioned contract package has a foreign source: " + name)
    else:
        expected_file = (expected / "__init__.py" if name == "verification.integrity"
                         else expected.with_suffix(".py"))
        origin = getattr(module, "__file__", None)
        require(isinstance(origin, str) and Path(origin).resolve() == expected_file,
                "versioned contract import has a foreign source: " + name)
        if name == "verification.integrity":
            require({Path(p).resolve() for p in getattr(module, "__path__", ())}
                        == {expected},
                    "versioned contract package path has a foreign source: " + name)


@contextmanager
def _contract_import_context():
    # The helper may audit a separate disposable active-30 checkout. Package
    # imports belong to this helper's checkout, not cwd or the inspected root.
    helper_root = Path(__file__).resolve().parents[2]
    names = ("verification", "verification.integrity", "verification.integrity.reports")
    original_path = sys.path[:]
    sys.path[:] = [str(helper_root), *(p for p in sys.path if p != str(helper_root))]
    try:
        for name in names:
            _check_import_origin(name, helper_root)
        if "verification" not in sys.modules:
            # verification is a namespace package. A foreign regular package
            # later on sys.path otherwise wins even when helper_root is first.
            spec = importlib.machinery.PathFinder.find_spec(
                "verification", [str(helper_root)])
            require(spec is not None and spec.origin is None
                    and list(spec.submodule_search_locations or ())
                        == [str(helper_root / "verification")],
                    "local verification namespace unavailable")
            spec.submodule_search_locations = [str(helper_root / "verification")]
            sys.modules["verification"] = importlib.util.module_from_spec(spec)
        yield
        for name in names:
            require(name in sys.modules, "versioned contract omitted import: " + name)
            _check_import_origin(name, helper_root)
    finally:
        sys.path[:] = original_path


def _json(root, head, path):
    raw = git(root, "show", head + ":" + path)
    require(0 < len(raw) <= 2_000_000, "unbounded staged manifest")
    try:
        item = strict_json_object(raw)
    except (UnicodeError, ValueError) as exc:
        raise ToolingMigrationError("noncanonical workflow manifest: " + path) from exc
    require(isinstance(item, dict), "workflow manifest is not an object")
    return item


def _blob(root, head, path):
    raw = git(root, "show", head + ":" + path)
    require(0 < len(raw) <= 1_000_000, "missing/oversized reviewed Git blob")
    oid = git(root, "rev-parse", head + ":" + path).decode().strip()
    require(SHA.fullmatch(oid) is not None, "invalid Git blob object identity")
    computed=hashlib.sha1(
        b"blob "+str(len(raw)).encode("ascii")+b"\0"+raw).hexdigest()
    require(computed==oid, "Git object contents differ from recorded blob OID")
    try:
        text = raw.decode("utf-8")
    except UnicodeError as exc:
        raise ToolingMigrationError("workflow is not UTF-8") from exc
    return oid, text


def _contract(root, head):
    manifest = _json(root, head, CONTRACT_MANIFEST)
    require(manifest.get("format") ==
            "Permansson.PR113.ReviewPendingVersionedWorkflowContract.v2"
            and manifest.get("installed") is False
            and manifest.get("independent_security_review") is False
            and manifest.get("owner_activation_authorized") is False
            and manifest.get("mathematical_acceptance") is False
            and manifest.get("publication_authorized") is False,
            "versioned proposal incorrectly asserts outside approval")
    oid, text = _blob(root, head, CONTRACT)
    require(oid == manifest.get("staged_git_blob_oid"),
            "versioned contract source differs from committed Git blob pin")
    source = root / CONTRACT
    require(source.is_file() and not source.is_symlink()
            and source.read_bytes() == text.encode("utf-8"),
            "versioned contract must load exact clean committed source")
    spec = importlib.util.spec_from_file_location(
        "pr113_review_pending_v2_exact_profile", source)
    require(spec is not None and spec.loader is not None,
            "versioned contract module unavailable")
    module = importlib.util.module_from_spec(spec)
    try:
        with _contract_import_context():
            spec.loader.exec_module(module)
    except ImportError as exc:
        raise ToolingMigrationError("versioned contract package import failed") from exc
    expected = manifest.get("expected_workflow_git_blobs")
    require(isinstance(expected, dict) and len(expected) == 30
            and expected == module.APPROVED_WORKFLOW_BLOBS,
            "30-source manifest and actual versioned contract disagree")
    return module, manifest


def _owner_approved_installation(root, head, originals):
    """The original 25 blobs, except the owner-approved archive workflow change.

    See archive_successor_approval_v1: the change must start from exactly the
    original preactivation blob. Without a committed policy nothing changes.
    """
    try:
        raw = git(root, "show", head + ":" + approval.POLICY_PATH)
    except ToolingMigrationError:
        return dict(originals)
    try:
        changes = approval.approved_workflow_changes(raw)
    except approval.ApprovalError as exc:
        raise ToolingMigrationError(str(exc)) from exc
    installed = dict(originals)
    for name, (before, after) in changes.items():
        require(originals.get(name) == before,
                "owner-approved workflow change does not start from the original blob")
        installed[name] = after
    return installed


def _historical(root, head):
    git(root, "merge-base", "--is-ancestor", PREACTIVATION_HEAD, head)
    old = exact_tree(root, PREACTIVATION_HEAD, ".github/workflows")
    require(len(old) == 25
            and all(mode == "100644" for mode, oid in old.values()),
            "preactivation historical 25-workflow reference is not intact")
    return {p.removeprefix(".github/workflows/"): oid
            for p, (mode, oid) in old.items()}



def source_phase(root, head):
    """Return the only two permissible inventory phases from real Git tree.

    This is a classification only, not approval. Always call audit() with the
    result before claiming even a source-bound engineering preflight.
    """
    root = Path(root).resolve(strict=True)
    require(isinstance(head, str) and SHA.fullmatch(head) is not None
            and git(root, "rev-parse", "HEAD").decode().strip() == head,
            "phase classification requires exact checked Git HEAD")
    tree = exact_tree(root, head, ".github/workflows")
    require(len(tree) in (25, 30)
            and all(mode == "100644" and
                    path.startswith(".github/workflows/") and
                    path.endswith((".yml", ".yaml"))
                    for path, (mode, oid) in tree.items()),
            "workflow source phase must be exactly 25 staged or 30 active Git blobs")
    return "staged" if len(tree) == 25 else "active"


def audited_source_phase(root, head):
    """Verify the complete exact Git phase, not merely its filename count."""
    phase = source_phase(root, head)
    return phase, audit(root, head, phase=phase)


def audit(root, head, *, phase="staged"):
    """Return an exact-content preview, never an activation certificate.

    staged: 25 active objects plus two source-staged replacements and five
    proposed additions make an exact virtual 30-object candidate.
    active: require 30 actual installed objects + matching installed guard/test;
    this remains review-pending until separate real external authorization.
    """
    root = Path(root).resolve(strict=True)
    require(phase in ("staged", "active")
            and isinstance(head, str) and SHA.fullmatch(head),
            "invalid successor workflow phase or source head")
    require(git(root, "rev-parse", "HEAD").decode().strip() == head,
            "current checkout is not the declared actual head")
    require(not git(root, "status", "--porcelain=v1", "--untracked-files=all"),
            "workflow review source is dirty/untracked")
    originals = _historical(root, head)
    module, manifest = _contract(root, head)
    full = _json(root, head, FULL_MANIFEST)
    proposals = _json(root, head, PROPOSAL_MANIFEST)
    replacements = full.get("full_replacements")
    additions = proposals.get("proposals")
    require(full.get("format") ==
                "Permansson.PR113.FullRequiredWorkflowPreactivation.v1"
            and full.get("independent_security_review") is False
            and full.get("owner_activation_authorized") is False
            and full.get("mathematical_acceptance") is False
            and full.get("publication_authorized") is False
            and isinstance(replacements, list) and len(replacements) == 2
            and proposals.get("format") ==
                "Permansson.PR113.UnreviewedWorkflowProposals.v1"
            and proposals.get("independent_security_review") is False
            and proposals.get("owner_authorized_activation") is False
            and isinstance(additions, list) and len(additions) == 5,
            "incomplete/incorrectly approved 2+5 workflow staging")
    replaced = {}
    for row in replacements:
        require(isinstance(row, dict)
                and row.get("installed") is False
                and row.get("independent_reviewed") is False,
                "unreviewed replacement says installed/approved")
        target = row.get("target")
        path = row.get("staged_source")
        require(isinstance(target, str)
                and target.startswith(".github/workflows/")
                and isinstance(path, str) and path.startswith(STAGE),
                "invalid exact replacement path")
        oid, text = _blob(root, head, path)
        name = target.removeprefix(".github/workflows/")
        require(name in originals and oid == row.get("git_blob_oid")
                and name not in replaced,
                "replacement SHA/name does not match exact 25-version history")
        replaced[name] = (oid, text)
    proposed = {}
    for row in additions:
        require(isinstance(row, dict) and
                row.get("installed") is False and row.get("approved") is False,
                "unreviewed new workflow says installed/approved")
        target = row.get("workflow_path")
        path = row.get("staged_source_path")
        require(isinstance(target, str)
                and target.startswith(".github/workflows/")
                and isinstance(path, str) and path.startswith(PROPOSALS),
                "invalid source of reviewed additional workflow")
        name = target.removeprefix(".github/workflows/")
        oid, text = _blob(root, head, path)
        require(name not in originals and name not in proposed
                and oid == row.get("git_blob_oid"),
                "new workflow duplicates original or mismatches staged Git blob")
        proposed[name] = (oid, text)
    require(set(replaced) == set(module.REPLACEMENT_WORKFLOWS)
            and set(proposed) == set(module.ADDITION_WORKFLOWS)
            and set(originals) - set(replaced) ==
                set(module.RETAINED_HISTORICAL_WORKFLOWS),
            "original/replacement/addition partition is not exactly 23+2+5")
    tree = exact_tree(root, head, ".github/workflows")
    if phase == "staged":
        require(len(tree) == 25 and
                {p.removeprefix(".github/workflows/"): v[1]
                 for p, v in tree.items()} ==
                    _owner_approved_installation(root, head, originals),
                "preactivation source cannot silently alter original 25 files")
        source = {}
        for name in originals:
            source[name] = _blob(root, head, ".github/workflows/" + name)[1]
        source.update({n: text for n, (oid, text) in replaced.items()})
        source.update({n: text for n, (oid, text) in proposed.items()})
    else:
        require(len(tree) == 30 and
                all(mode == "100644" for mode, oid in tree.values())
                and {p.removeprefix(".github/workflows/") for p in tree} ==
                    set(module.APPROVED_WORKFLOW_BLOBS),
                "activated source is not exactly the 30 reviewed workflow objects")
        source = {}
        for name in module.APPROVED_WORKFLOW_BLOBS:
            path = ".github/workflows/" + name
            oid, text = _blob(root, head, path)
            require(tree[path] == ("100644", oid)
                    and module.git_blob_oid(text.encode("utf-8")) == oid,
                    "activated workflow differs from committed exact blob")
            source[name] = text
        for name in module.RETAINED_HISTORICAL_WORKFLOWS:
            require(tree[".github/workflows/" + name][1] == originals[name],
                    "a retained historical workflow was changed")
        installations = {
            "verification/integrity/workflow_contract.py": CONTRACT,
            "verification/integrity/tests/test_workflow.py":
                STAGE + "test_workflow_v2.py",
            "verification/research/test_localized_prefix_compiler.py":
                STAGE + "test_localized_prefix_compiler.py",
        }
        for installed, staged in installations.items():
            require(git(root, "rev-parse", head + ":" + installed).strip() ==
                    git(root, "rev-parse", head + ":" + staged).strip(),
                    "source migration incomplete or test/contract unreviewed: "
                    + installed)
    # Authenticate the versioned historical artifact transport separately
    # from workflow YAMLs; the installed job must not borrow a v1 event gate.
    transport_path="verification/research/pr113_historical_artifact_delivery_v2.py"
    transport_oid,transport_text=_blob(root,head,transport_path)
    require(module.git_blob_oid(transport_text.encode("utf-8"))==transport_oid
            and 'FORMAT = "Permansson.PR113.ExactHistoricalArtifactDelivery.v2"'
                in transport_text
            and "from pr113_required_dual_gate_v2 import actual_ci_event"
                in transport_text
            and "from pr113_historical_postmerge_v2 import exact_main_event"
                in transport_text,
            "versioned transport source differs from exact Git blob or v2 event gate")
    approved = module.validate_workflow_set(source)
    actual = {name: module.git_blob_oid(text.encode("utf-8"))
              for name, text in sorted(source.items())}
    require(actual == module.APPROVED_WORKFLOW_BLOBS,
            "30 workflow full blob map has unexpected values")
    profile_digest = hashlib.sha256(json.dumps(
        actual, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return {
        "format": FORMAT,
        "status": ("EXACT_STAGED_25_TO_30_CANDIDATE_UNAPPROVED"
                   if phase == "staged" else
                   "EXACT_ACTIVE_30_CANDIDATE_SECURITY_REVIEW_PENDING"),
        "head_sha": head,
        "historical_original_head": PREACTIVATION_HEAD,
        "historical_original_workflow_count": 25,
        "current_reviewed_workflow_count": 30,
        "retained_historical_count": 23,
        "replacement_count": 2,
        "addition_count": 5,
        "versioned_source_phase": phase,
        "current_source_profile_sha256": profile_digest,
        "expected_source_blobs": actual,
        "inherited_mutable_action_refs":
            approved["retained_historical_mutable_action_refs"],
        "all_actions_commit_pinned":
            approved["all_workflow_actions_commit_pinned"],
        "historical_T_A2_verification": "SEPARATE_DUAL_EXECUTION_REQUIRED",
        "independent_security_review": False,
        "owner_activation_authorized": False,
        "mathematical_acceptance": False,
        "merge_authorized": False,
        "publication_authorized": False,
    }

"""Choose the real A2 compiler from an audited Git source profile.

The staged-25 compiler and active-30 compiler have intentionally incompatible
source identities. Never fall back from one to the other after a failure.
This module does not replace historical A2, approve a migration, or accept CI.
"""
from __future__ import annotations

from dataclasses import dataclass
import importlib
from pathlib import Path
import re
import subprocess
from types import ModuleType

PROFILE_FORMAT = "Permansson.PR113.VersionedWorkflowEvidence.v2"
PHASES = {
    "staged": (
        "EXACT_STAGED_25_TO_30_CANDIDATE_UNAPPROVED",
        "pr113_a2_successor_compiler",
        "Permansson.PR113.A2SuccessorCompilerCandidate.v1",
    ),
    "active": (
        "EXACT_ACTIVE_30_CANDIDATE_SECURITY_REVIEW_PENDING",
        "pr113_a2_successor_compiler_v2",
        "Permansson.PR113.A2SuccessorCompilerCandidate.v2",
    ),
}
SHA = re.compile(r"^[0-9a-f]{40}$")


class CompilerRouteError(ValueError):
    pass


@dataclass(frozen=True)
class CompilerRoute:
    phase: str
    checked_sha: str
    module: ModuleType
    receipt_format: str


def _head(repo: Path) -> str:
    try:
        raw = subprocess.check_output(
            ["git", "-C", str(repo), "rev-parse", "--verify", "HEAD"],
            stderr=subprocess.PIPE, timeout=20,
        )
        value = raw.decode("ascii").strip()
    except (OSError, UnicodeError, subprocess.SubprocessError) as exc:
        raise CompilerRouteError("real A2 checkout HEAD unavailable") from exc
    if SHA.fullmatch(value) is None:
        raise CompilerRouteError("A2 checkout is not a complete Git commit ID")
    return value


def _audited_profile(repo: Path, head: str):
    # Audit exact Git objects, modes, manifests and installed guard sources;
    # counting files or trusting a receipt's status is not sufficient.
    from pr113_workflow_profile_v2 import audited_source_phase
    return audited_source_phase(repo, head)


def select_compiler(repo: Path) -> CompilerRoute:
    root = Path(repo).resolve(strict=True)
    head = _head(root)
    phase, profile = _audited_profile(root, head)
    if type(phase) is not str or phase not in PHASES:
        raise CompilerRouteError("unsupported A2 workflow source phase")
    expected_status, module_name, receipt_format = PHASES[phase]
    if (type(profile) is not dict
            or profile.get("format") != PROFILE_FORMAT
            or profile.get("status") != expected_status
            or profile.get("head_sha") != head
            or profile.get("versioned_source_phase") != phase
            or type(profile.get("historical_original_workflow_count")) is not int
            or profile["historical_original_workflow_count"] != 25
            or type(profile.get("current_reviewed_workflow_count")) is not int
            or profile["current_reviewed_workflow_count"] != 30
            or profile.get("independent_security_review") is not False):
        raise CompilerRouteError("A2 compiler route is not bound to audited source")
    compiler = importlib.import_module(module_name)
    historical = importlib.import_module("localized_prefix_gate")
    if (compiler.DECLS != historical.DECLS
            or compiler.MUTATIONS != historical.MUTATIONS
            or len(compiler.DECLS) != 40 or len(compiler.MUTATIONS) != 4
            or not callable(compiler.verify)):
        raise CompilerRouteError("A2 compiler changed the original proof/control scope")
    if _head(root) != head:
        raise CompilerRouteError("A2 checkout moved during compiler selection")
    return CompilerRoute(phase, head, compiler, receipt_format)

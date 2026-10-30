"""One entry point for every source-bound Lean candidate family.

`emit` dispatches to the family's emitter and `recheck` to its independent
byte/semantic binding check. Neither runs Lean, and both keep the family's
own `lean_status: NOT_EXECUTED` result: a compiled candidate is evidence only
from `lake env lean` on the emitted file under the pinned toolchain, and never
independent certification, empirical identification or release acceptance.
"""
from __future__ import annotations
from pathlib import Path

from ..errors import AppError
from . import control_source_check, finite_emit, finite_source_check, lp_emit, lp_source_check
from .control_source_check import FAMILIES, REGION_FAMILIES

# Families outside the shared control layout; the finite-world candidate binds only the model.
EXTRA_FAMILIES = ('finite-world', 'lp')
RECEIPTLESS = {'finite-world'}


def families() -> list[str]:
    return sorted(set(FAMILIES) | set(EXTRA_FAMILIES))


def _arity(family: str, receipt: Path | None, region: Path | None):
    if family not in families():
        raise AppError('REIFY_FAMILY', 'unknown source-candidate family')
    if (receipt is None) != (family in RECEIPTLESS):
        raise AppError('REIFY_FAMILY', 'a receipt is required for every family except finite-world')
    if (region is not None) != (family in REGION_FAMILIES):
        raise AppError('REIFY_FAMILY', 'a region file is required exactly for region families')


def emit(family: str, request: Path, receipt: Path | None, output: Path,
         region: Path | None = None) -> dict:
    _arity(family, receipt, region)
    if family == 'finite-world':
        return finite_emit.emit_file(request, output)
    if family == 'lp':
        return lp_emit.emit_files(request, receipt, output)
    emitter = FAMILIES[family][1]
    if family in REGION_FAMILIES:
        return emitter.emit_files(request, region, receipt, output)
    return emitter.emit_files(request, receipt, output)


def recheck(family: str, request: Path, receipt: Path | None, candidate: Path,
            region: Path | None = None) -> dict:
    _arity(family, receipt, region)
    if family == 'finite-world':
        return finite_source_check.check_files(request, candidate)
    if family == 'lp':
        return lp_source_check.check_files(request, receipt, candidate)
    return control_source_check.check_family(family, request, receipt, candidate, region)

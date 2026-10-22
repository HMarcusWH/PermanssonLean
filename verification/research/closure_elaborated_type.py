"""Read complete elaborated declaration types from a genuine pinned Lean environment.

This exporter uses the kernel Environment's ConstantInfo rather than slicing
source at the first textual ':=' (which may occur inside a named argument).
The Lean AST representation includes all elaborated binders, levels, and terms.
The byte digest is a deterministic *compiler evidence candidate*, not itself
an approved review, axiom audit, or final CI attestation.
"""
from __future__ import annotations

import hashlib
import json
import re

BEGIN = "PERMANSSON_ELABORATED_TYPE_V1_BEGIN"
END = "PERMANSSON_ELABORATED_TYPE_V1_END"
DECL = re.compile(r"^[A-Za-z0-9_'.]+\.[A-Za-z0-9_']+$")
MODULE = re.compile(r"^[A-Za-z0-9_'.]+$")
TYPES = frozenset((
    "axiom", "definition", "theorem", "opaque",
    "quotient", "inductive", "constructor", "recursor",
))


class TypeEvidenceError(ValueError):
    pass


def lean_probe(module: str, declaration: str) -> str:
    if not MODULE.fullmatch(module) or not DECL.fullmatch(declaration):
        raise TypeEvidenceError("invalid compiler module or qualified declaration")
    # The interpolated declaration is an exact checked identifier, not model text.
    # The Repr Expr instance in pinned Lean 4 serializes the elaborated AST.
    return (
        "import Lean\n"
        f"import {module}\n"
        "open Lean Elab Command\n"
        "run_cmd do\n"
        f"  let nm : Name := `{declaration}\n"
        "  let some info := (← getEnv).find? nm |\n"
        "    throwError \"no kernel declaration for requested name\"\n"
        "  let kind : String := match info with\n"
        "    | .axiomInfo _ => \"axiom\"\n"
        "    | .defnInfo _ => \"definition\"\n"
        "    | .thmInfo _ => \"theorem\"\n"
        "    | .opaqueInfo _ => \"opaque\"\n"
        "    | .quotInfo _ => \"quotient\"\n"
        "    | .inductInfo _ => \"inductive\"\n"
        "    | .ctorInfo _ => \"constructor\"\n"
        "    | .recInfo _ => \"recursor\"\n"
        "  logInfo m!\"" + BEGIN +
        "\\nNAME={info.name.toString}\\nKIND={kind}" +
        "\\nUNIVERSES={reprStr info.levelParams}" +
        "\\nTYPE={reprStr info.type}\\n" + END + "\"\n"
        f"#print axioms {declaration}\n"
    )


def compiled_type_record(log: str, declaration: str) -> dict:
    if not isinstance(log, str) or not DECL.fullmatch(declaration):
        raise TypeEvidenceError("invalid Lean type export input")
    if len(log.encode("utf-8")) > 4 * 1024 * 1024:
        raise TypeEvidenceError("compiler type diagnostic exceeds bound")
    pattern = re.compile(
        re.escape(BEGIN) + r"\nNAME=(?P<name>[^\n]+)" +
        r"\nKIND=(?P<kind>[^\n]+)" +
        r"\nUNIVERSES=(?P<universes>.*?)" +
        r"\nTYPE=(?P<type>.*?)\n" + re.escape(END),
        re.DOTALL,
    )
    matches = list(pattern.finditer(log))
    if len(matches) != 1:
        raise TypeEvidenceError("missing/duplicate complete compiled type record")
    item = matches[0].groupdict()
    if item["name"] != declaration or item["kind"] not in TYPES or \
       not item["universes"].strip() or not item["type"].strip():
        raise TypeEvidenceError("wrong target, kind, universes or empty elaborated type")
    return {
        "declaration": item["name"],
        "declaration_kind": item["kind"],
        "universe_params_repr": item["universes"],
        "type_expr_repr": item["type"],
    }


def elaborated_type_sha256(record: dict) -> str:
    if not isinstance(record, dict) or set(record) != {
        "declaration", "declaration_kind",
        "universe_params_repr", "type_expr_repr",
    }:
        raise TypeEvidenceError("invalid canonical type-record shape")
    raw = json.dumps(record, sort_keys=True, ensure_ascii=False,
                     separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()

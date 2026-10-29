"""Numeric-only native C10/C11 orchestration and independent receipt replay."""
from __future__ import annotations
from hashlib import sha256
import json
from pathlib import Path
import sys
from .contracts import parse_request
from .capabilities import selected
from .errors import AppError
from .process import run_bounded
from .source import check_source
from .strict_json import strict_read


def _json_bytes(value) -> bytes:
    return (json.dumps(value, sort_keys=True, ensure_ascii=False, indent=2) + "\n").encode("utf-8")


def execute(request_path: Path, source_root: Path, output: Path):
    if request_path.is_symlink() or not request_path.is_file():
        raise AppError("REQUEST_PATH", "request must be a regular file")
    _, data = strict_read(request_path)
    request = parse_request(data, request_file=request_path)
    cap = selected(request.capability)
    raw, _ = strict_read(request.model_path)
    repo = source_root.resolve()
    out = output.absolute()
    if repo == out or repo in out.parents:
        raise AppError("OUTPUT_SCOPE", "output must be outside repository")
    if out.exists():
        raise AppError("OUTPUT_SCOPE", "output path must not exist")
    # Verify pins before touching output or executing an arbitrary provider.
    before = check_source(repo, cap["sha256_pins"])
    out.mkdir(parents=True, exist_ok=False)
    native = out / "native"
    native.mkdir()
    # Reified input is an immutable copy, not a mutable caller path during execution.
    frozen_input = out / "model.input.json"
    frozen_input.write_bytes(raw)
    command = [sys.executable, "-I", "-B", str(repo / cap["native_cli"]), str(frozen_input),
               "--mode", "numeric", "--output", str(native)]
    producer = run_bounded(command, repo, out / "producer.log")
    receipt = native / "numeric_receipt.json"
    result_file = native / "result.json"
    if not receipt.is_file() or not result_file.is_file():
        raise AppError("RECEIPT_MISSING", "native application did not provide both expected files")
    _, report = strict_read(result_file)
    raw_receipt, actual_receipt = strict_read(receipt)
    if type(report) is not dict or type(actual_receipt) is not dict:
        raise AppError("RECEIPT_INVALID", "native report must be a JSON object")
    if report.get("scientific_claims_verified") is not False or report.get("empirical_identification") != "NOT_IDENTIFIED":
        raise AppError("RECEIPT_INVALID", "native scientific status is inconsistent")
    if report.get("numeric_status") not in cap["allowed_numeric_status"]:
        raise AppError("RECEIPT_INVALID", "native numeric status is unsupported")
    if report.get("lean_status") not in ("NOT_EXECUTED", "NOT_RUN"):
        raise AppError("RECEIPT_INVALID", "numeric mode falsely claims Lean replay")
    if report.get("input_sha256") != actual_receipt.get("input_sha256"):
        raise AppError("RECEIPT_INVALID", "native input digest disagreement")
    # Recheck the bytes saved by the native process, not an in-memory producer object.
    check = run_bounded([sys.executable, "-B", str(repo / cap["checker"]), str(receipt)],
                        repo, out / "checker.log")
    after = check_source(repo, cap["sha256_pins"])
    if before != after or frozen_input.read_bytes() != raw:
        raise AppError("SOURCE_CHANGED", "source or frozen input changed across execution")
    artifacts = {}
    for name, f in {"model": frozen_input, "native_receipt": receipt, "native_result": result_file,
                    "producer_log": out / "producer.log", "checker_log": out / "checker.log"}.items():
        artifacts[name] = {"file": str(f.relative_to(out)), "sha256": sha256(f.read_bytes()).hexdigest()}
    value = {
        "format": "Permansson.App.NumericResult.Reconstructed.v1",
        "capability": request.capability,
        "source_profile": cap["source_profile"],
        "source_pin_sha256": before,
        "model_bytes_sha256": sha256(raw).hexdigest(),
        "native_input_sha256": report["input_sha256"],
        "numeric_status": "EXACT_RATIONAL_VERIFIED",
        "lean_status": "NOT_EXECUTED",
        "scientific_claims_verified": False,
        "empirical_identification": "NOT_IDENTIFIED",
        "independent_application_acceptance": "NOT_ASSESSED",
        "release_acceptance": "NOT_ASSESSED",
        "producer": producer, "checker": check,
        "native_summary": report,
        "artifacts": artifacts,
    }
    (out / "application_result.json").write_bytes(_json_bytes(value))
    return value

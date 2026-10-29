"""Permansson numeric application recovery: original v2 binary not available."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys
from .capabilities import registry
from .errors import AppError
from .package_data import export_resources, NAMES
from .runner import execute


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    sub.add_parser("capabilities")
    resources = sub.add_parser("resources")
    resources.add_argument("--output", type=Path)
    run = sub.add_parser("run")
    run.add_argument("request", type=Path)
    run.add_argument("--source-root", type=Path, required=True)
    run.add_argument("--output", type=Path, required=True)
    args = p.parse_args(argv)
    try:
        if args.command == "capabilities":
            print(json.dumps(registry(), indent=2, sort_keys=True))
        elif args.command == "resources":
            result = export_resources(args.output) if args.output else list(NAMES)
            print(json.dumps(result, indent=2, sort_keys=True))
        else:
            result = execute(args.request, args.source_root, args.output)
            print(json.dumps({"ok":True,"numeric_status":result["numeric_status"],
                              "lean_status":result["lean_status"],
                              "result_file":str(args.output / "application_result.json")}, sort_keys=True))
        return 0
    except AppError as exc:
        print(json.dumps({"ok":False,"error":{"code":exc.code,"message":str(exc)}},sort_keys=True),file=sys.stderr)
        return 2

if __name__ == "__main__":
    raise SystemExit(main())

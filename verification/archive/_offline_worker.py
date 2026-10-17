"""Privilege-dropped worker; attest isolation before parsing a supplement."""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import sys

# A direct script invocation needs only this known source root, never cwd or
# candidate PYTHONPATH. The launcher has already dropped all root privileges.
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from verification.integrity.reports import HardeningError, check_report, write_report
from verification.archive.offline_smoke import isolation_attestation
from verification.archive.verify_bundle import verify_supplement


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--supplement", required=True)
    parser.add_argument("--scratch", required=True)
    parser.add_argument("--report", required=True)
    parser.add_argument("--parent-netns", required=True)
    parser.add_argument("--source-repo")
    parser.add_argument("--source-candidate")
    args = parser.parse_args(argv)
    try:
        isolation = isolation_attestation(args.parent_netns)
        os.environ["PERMANSSON_PARENT_NETNS"] = args.parent_netns
        details = verify_supplement(args.supplement, args.scratch, require_isolation=True,
                                    source_repo=args.source_repo, source_candidate=args.source_candidate)
        details["isolation"] = isolation
        payload = check_report("archive-reproducibility", details=details,
                               completed_stages=details["completed_stages"])
        code = 0
    except HardeningError as exc:
        payload = check_report("archive-reproducibility", None, "BLOCKED" if exc.exit_code == 3 else "FAIL", exc)
        code = exc.exit_code
    except Exception as exc:
        payload = check_report("archive-reproducibility", None, "FAIL", HardeningError("E_UNEXPECTED", str(exc)))
        code = 1
    write_report(args.report, payload)
    return code


if __name__ == "__main__":
    raise SystemExit(main())

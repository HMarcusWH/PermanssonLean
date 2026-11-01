"""Internal entry point of the budgeted child process; not a public command.

`permansson-app` starts this module in a limited child process (see
`permansson_app.budget.run_budgeted`). It reads the staging path and limits the
parent handed over, validates them, applies every limit to itself and then runs
the requested exact profile command, writing only into the private staging
directory. Started any other way it either refuses or stays within the limits
named in its configuration.
"""
from __future__ import annotations

import json
import os
import sys

from .budget import CHILD_CONFIG_ENV, child_config
from .errors import AppError
from .__main__ import _main


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    try:
        child = child_config(os.environ.get(CHILD_CONFIG_ENV))
    except AppError as exc:
        print(json.dumps({'ok': False, 'error': {'code': exc.code, 'message': str(exc)}}, sort_keys=True),
              file=sys.stderr)
        return 2
    return _main(argv, child)


if __name__ == '__main__':
    raise SystemExit(main())

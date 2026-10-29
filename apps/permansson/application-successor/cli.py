"""Development-source entry point; installed packages use `permansson-app`."""
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "src"))
from permansson_app.__main__ import main
if __name__ == "__main__":
    raise SystemExit(main())

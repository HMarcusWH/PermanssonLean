"""Verification entry point for the reconstructed source overlay."""
from pathlib import Path
import os
import subprocess
import sys
base=Path(__file__).resolve().parents[1]
result=subprocess.run([sys.executable,'-m','unittest','discover','-s',str(base/'tests'),'-v'],
                      cwd=base,env=os.environ.copy(),check=False)
raise SystemExit(result.returncode)

from pathlib import Path
import runpy
runpy.run_path(str(Path(__file__).resolve().parent / 'scripts' / 'run_all_v17.py'), run_name='__main__')

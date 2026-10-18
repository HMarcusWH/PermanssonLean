"""Check or extend the research root's mandatory direct import inventory."""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    path = ROOT / 'PermanssonResearch.lean'
    raw = path.read_bytes()
    imported = {name for line in raw.decode('utf-8').splitlines()
                if line.strip().startswith('import ') for name in line.strip()[7:].split()}
    modules = sorted('.'.join(p.relative_to(ROOT).with_suffix('').parts)
                     for p in (ROOT / 'PermanssonResearch').rglob('*.lean'))
    missing = sorted(set(modules) - imported)
    if missing and not args.write:
        raise SystemExit('Missing direct imports: ' + ', '.join(missing))
    if missing:
        newline = b'\r\n' if b'\r\n' in raw else b'\n'
        additions = newline.join(('import ' + name).encode('utf-8') for name in missing)
        marker = raw.index(b'/-!')
        path.write_bytes(raw[:marker] + additions + newline + newline + raw[marker:])
    print('Research direct import inventory:', len(modules), 'modules;', len(missing), 'added')


if __name__ == '__main__':
    main()

#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
python -B "$ROOT/render/assemble_spec.py"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
pandoc "$ROOT/MATHEMATICAL_BUILD_SPEC.md" \
  --from=markdown+tex_math_dollars+raw_tex --standalone --to=latex \
  --pdf-engine=xelatex --top-level-division=section --toc --toc-depth=2 \
  -V documentclass=article -V papersize=a4 -V fontsize=11pt \
  -V geometry:margin=24mm -V mainfont='Liberation Serif' \
  -V sansfont='Liberation Sans' -V monofont='DejaVu Sans Mono' \
  -V colorlinks=true -V linkcolor=PermanssonInk -V urlcolor=PermanssonInk \
  -H "$ROOT/render/header.tex" -B "$ROOT/render/titlepage.tex" \
  -o "$ROOT/render/MATHEMATICAL_BUILD_SPEC.tex"
python - "$ROOT/render/MATHEMATICAL_BUILD_SPEC.tex" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1]);s=p.read_text()
# Wrap long inline source identifiers; their exact strings remain in JSON/Markdown.
s=s.replace('\\texttt{','\\codewrap{')
s=s.replace('\\tableofcontents', '\\begingroup\\small\\tableofcontents\\endgroup\\clearpage')
p.write_text(s)
PY
cd "$WORK"
for pass in 1 2 3; do
  xelatex -interaction=nonstopmode -halt-on-error "$ROOT/render/MATHEMATICAL_BUILD_SPEC.tex" > "compile${pass}.stdout" 2>&1
done
cp MATHEMATICAL_BUILD_SPEC.pdf "$ROOT/MATHEMATICAL_BUILD_SPEC.pdf"
cp MATHEMATICAL_BUILD_SPEC.log "$ROOT/render/compile.log"

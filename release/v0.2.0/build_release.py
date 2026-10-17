"""Build the separately versioned v0.2.0 research companion from one JSON source."""
from __future__ import annotations

import argparse
import csv
import importlib.metadata
import io
import json
import platform
import sys
from html import escape
from pathlib import Path

from verify_release import (BASELINE, SHA, blob, csv_row, digest, git, plain,
                            protected_snapshot, source_providers, strings,
                            tex_escape, validate_acceptance, validate_c10_archives, validate_manuscript,
                            validate_supporting_evidence,
                            verify, require)

STEM = "Permansson_Research_Companion_v0.2.0"


def tex_document(data, revision, manuscript_hash, draft):
    esc = lambda value: tex_escape(plain(value))
    lines = [f"% Source-SHA: {revision}", f"% Manuscript-SHA256: {manuscript_hash}",
             f"% Version: {data['version']}", f"% Mode: {'draft' if draft else 'final'}",
             r"\documentclass[11pt,a4paper]{article}",
             r"\usepackage[margin=25mm]{geometry}", r"\usepackage{fontspec}",
             r"\setmainfont{DejaVu Serif}", r"\setsansfont{DejaVu Sans}",
             r"\usepackage{amsmath,amssymb,booktabs,enumitem,xcolor,hyperref,graphicx}",
             r"\hypersetup{colorlinks=true,linkcolor=blue,urlcolor=blue}",
             r"\setlength{\parindent}{0pt}\setlength{\parskip}{7pt}",
             r"\setlist{noitemsep,topsep=3pt}",
             r"\setcounter{secnumdepth}{0}\raggedright\emergencystretch=3em",
             r"\newsavebox{\companionEqBox}",
             r"\newcommand{\companionEquation}[1]{\begin{center}\sbox{\companionEqBox}{$\displaystyle #1$}\ifdim\wd\companionEqBox>\linewidth\resizebox{\linewidth}{!}{\usebox{\companionEqBox}}\else\usebox{\companionEqBox}\fi\end{center}}",
             r"\title{" + esc(data["title"]) + r"\\[5pt]\large " + esc(data["subtitle"]) + "}",
             r"\author{" + esc(data["author"]) + "}", r"\date{" + esc(data["date"]) + "}",
             r"\begin{document}\maketitle"]
    if draft:
        lines.append(r"\begin{center}\textbf{DRAFT - acceptance evidence is incomplete.}\end{center}")
    lines += [r"\begin{abstract}" + esc(data["abstract"]) + r"\end{abstract}",
              r"{\footnotesize Source: \texttt{" + esc(revision) + r"}. Version: 0.2.0.}"]
    for section in data["sections"]:
        lines.append(r"\section{" + esc(section["title"]) + "}")
        lines.extend(esc(p) + "\n" for p in section.get("paragraphs", []))
        for equation in section.get("equations", []):
            latex = equation["latex"].strip().strip("$")
            lines += [r"\companionEquation{" + latex + "}", r"{\small " + esc(equation.get("caption", "")) + "}"]
        for claim in section.get("claims", []):
            lines += [r"\subsection*{" + esc(claim["anchor"] + " - " + claim["title"] +
                                             " [" + claim["status"] + "]") + "}",
                      esc(claim["statement"]) + "\n"]
            for field, label in (("assumptions", "Assumptions"), ("proof", "Proof or derivation"), ("open", "Open boundary")):
                values = strings(claim.get(field, []), field)
                if values:
                    lines.append(r"\textbf{" + label + ".} " + "\n\n".join(esc(p) for p in values))
            if claim.get("providers"):
                lines.append(r"\textbf{Source providers.}")
                lines.extend(r"{\footnotesize\raggedright " + esc(p["module"]) + r"\\ " +
                             esc(p["declaration"]) + r"\par}" for p in claim["providers"])
    lines += [r"\end{document}", ""]
    return "\n".join(lines)


def pdf_document(data, revision, manuscript_hash, draft, output):
    import matplotlib
    from matplotlib import mathtext
    from matplotlib.font_manager import FontProperties
    from pypdf import PdfReader, PdfWriter
    from reportlab.lib import colors
    from reportlab.lib.enums import TA_CENTER, TA_LEFT
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
    from reportlab.lib.units import mm
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    from reportlab.platypus import (Image, KeepTogether, Paragraph, SimpleDocTemplate,
                                    Spacer)

    font_dir = Path(matplotlib.get_data_path()) / "fonts/ttf"
    for name, filename in (("CompanionSerif", "DejaVuSerif.ttf"),
                           ("CompanionSerif-Bold", "DejaVuSerif-Bold.ttf"),
                           ("CompanionSerif-Italic", "DejaVuSerif-Italic.ttf"),
                           ("CompanionSans", "DejaVuSans.ttf"),
                           ("CompanionSans-Bold", "DejaVuSans-Bold.ttf"),
                           ("CompanionMono", "DejaVuSansMono.ttf")):
        pdfmetrics.registerFont(TTFont(name, str(font_dir / filename)))
    pdfmetrics.registerFontFamily("CompanionSerif", normal="CompanionSerif", bold="CompanionSerif-Bold",
                                  italic="CompanionSerif-Italic", boldItalic="CompanionSerif-Bold")
    pdfmetrics.registerFontFamily("CompanionSans", normal="CompanionSans", bold="CompanionSans-Bold")
    navy, muted, pale = colors.HexColor("#17334B"), colors.HexColor("#526675"), colors.HexColor("#EEF3F6")
    styles = getSampleStyleSheet()
    styles.add(ParagraphStyle("CompBody", fontName="CompanionSerif", fontSize=9.7, leading=14.3,
                              spaceAfter=7.5, textColor=colors.HexColor("#202D36"), allowWidows=0, allowOrphans=0))
    styles.add(ParagraphStyle("CompTitle", fontName="CompanionSans-Bold", fontSize=23, leading=29,
                              textColor=navy, spaceAfter=12))
    styles.add(ParagraphStyle("CompSubtitle", fontName="CompanionSans", fontSize=11.2, leading=16,
                              textColor=muted, spaceAfter=13))
    styles.add(ParagraphStyle("CompMeta", fontName="CompanionSans", fontSize=8, leading=12,
                              textColor=muted, spaceAfter=8))
    styles.add(ParagraphStyle("CompSection", fontName="CompanionSans-Bold", fontSize=14, leading=19,
                              textColor=navy, spaceBefore=18, spaceAfter=9, keepWithNext=True))
    styles.add(ParagraphStyle("CompClaim", fontName="CompanionSans-Bold", fontSize=10.1, leading=14,
                              textColor=navy, spaceBefore=10, spaceAfter=6, keepWithNext=True))
    styles.add(ParagraphStyle("CompProvider", fontName="CompanionMono", fontSize=7.3, leading=10.5,
                              spaceAfter=5, textColor=muted, wordWrap="CJK"))
    styles.add(ParagraphStyle("CompCaption", fontName="CompanionSans", fontSize=8.1, leading=12,
                              alignment=TA_CENTER, textColor=muted, spaceAfter=10))
    styles.add(ParagraphStyle("CompAbstract", parent=styles["CompBody"], fontSize=9.4, leading=14.2,
                              backColor=pale, borderPadding=12, spaceBefore=5, spaceAfter=17))

    para = lambda text, style="CompBody": Paragraph(escape(plain(text)).replace("\n", "<br/>"), styles[style])
    story = [para(data["title"], "CompTitle"), para(data["subtitle"], "CompSubtitle"),
             para(data["author"] + "  |  " + data["date"] + "  |  Version " + data["version"], "CompMeta")]
    if draft:
        story.append(para("DRAFT - acceptance evidence is incomplete.", "CompClaim"))
    story += [para(data["abstract"], "CompAbstract"),
              para("Research source: " + revision, "CompMeta")]
    for section in data["sections"]:
        story.append(para(section["title"], "CompSection"))
        story.extend(para(p) for p in section.get("paragraphs", []))
        for equation in section.get("equations", []):
            image = io.BytesIO()
            mathtext.math_to_image("$" + equation["latex"].strip().strip("$") + "$", image,
                                   prop=FontProperties(size=16), dpi=240, format="png", color="#17334B")
            image.seek(0)
            flow = Image(image)
            scale = min(72 / 240, (160 * mm) / flow.imageWidth, (35 * mm) / flow.imageHeight)
            flow.drawWidth, flow.drawHeight = flow.imageWidth * scale, flow.imageHeight * scale
            story.append(KeepTogether([Spacer(1, 3 * mm), flow,
                                      para(equation.get("caption", ""), "CompCaption")]))
        for claim in section.get("claims", []):
            story.append(para(claim["anchor"] + " - " + claim["title"] + " [" + claim["status"] + "]", "CompClaim"))
            story.append(para(claim["statement"]))
            for field, label in (("assumptions", "Assumptions"), ("proof", "Proof or derivation"), ("open", "Open boundary")):
                values = strings(claim.get(field, []), field)
                if values:
                    text = "<b>" + label + ".</b> " + "<br/>".join(escape(plain(p)) for p in values)
                    story.append(Paragraph(text, styles["CompBody"]))
            if claim.get("providers"):
                story.append(KeepTogether([Paragraph("<b>Source providers.</b>", styles["CompBody"])] +
                    [para(p["module"] + "\n" + p["declaration"], "CompProvider") for p in claim["providers"]]))

    def footer(canvas, doc):
        canvas.saveState()
        width, height = A4
        canvas.setStrokeColor(colors.HexColor("#D5DFE6"))
        canvas.line(23 * mm, 20 * mm, width - 23 * mm, 20 * mm)
        canvas.setFont("CompanionSans", 7)
        canvas.setFillColor(muted)
        canvas.drawString(23 * mm, 15.5 * mm, "Permansson | Research companion v0.2.0" + (" | DRAFT" if draft else ""))
        canvas.drawRightString(width - 23 * mm, 15.5 * mm, str(doc.page))
        canvas.restoreState()

    buffer = io.BytesIO()
    doc = SimpleDocTemplate(buffer, pagesize=A4, leftMargin=23 * mm, rightMargin=23 * mm,
                            topMargin=23 * mm, bottomMargin=27 * mm, title=data["title"],
                            author=data["author"], subject=data["subtitle"], invariant=1)
    doc.build(story, onFirstPage=footer, onLaterPages=footer)
    writer = PdfWriter()
    writer.clone_document_from_reader(PdfReader(io.BytesIO(buffer.getvalue())))
    writer.add_metadata({"/Title": data["title"], "/Author": data["author"], "/Subject": data["subtitle"],
                         "/PermanssonDate": data["date"],
                         "/PermanssonSourceSHA": revision, "/PermanssonManuscriptSHA256": manuscript_hash,
                         "/PermanssonVersion": data["version"], "/PermanssonMode": "draft" if draft else "final"})
    with output.open("wb") as stream:
        writer.write(stream)


def build(kit, draft, source):
    root = Path(git(kit, "rev-parse", "--show-toplevel").decode().strip())
    manuscript_path = kit / "manuscript.json"
    data = json.loads(manuscript_path.read_text(encoding="utf-8"))
    pending = validate_manuscript(data, draft, manuscript_path.read_bytes())
    evidence_path = kit / "acceptance-evidence.json"
    evidence = json.loads(evidence_path.read_text(encoding="utf-8")) if evidence_path.exists() else None
    revision = source or (evidence or {}).get("accepted_source_sha")
    if revision is None:
        require(draft, "Final build requires an accepted source revision")
        revision = git(root, "rev-parse", "HEAD").decode().strip()
    require(SHA.fullmatch(revision), "Use the full immutable 40-character source SHA")
    validate_acceptance(root, evidence, revision, draft, data)
    validate_c10_archives(kit, root, evidence, draft)
    protected = protected_snapshot(root, revision)
    rows, missing = source_providers(root, revision, data, draft)
    manuscript_hash = digest(manuscript_path.read_bytes())
    output = kit / "output/pdf"
    output.mkdir(parents=True, exist_ok=True)
    (output / f"{STEM}.tex").write_text(tex_document(data, revision, manuscript_hash, draft), encoding="utf-8", newline="\n")
    pdf_document(data, revision, manuscript_hash, draft, output / f"{STEM}.pdf")
    (output / "theorem-map.json").write_text(json.dumps({"version": data["version"], "source_sha": revision,
                                                         "claims": rows}, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
    csv_rows = [csv_row(row, provider) for row in rows for provider in row["source_providers"] or [{}]]
    fields = ("anchor", "title", "status", "statement", "assumptions", "proof", "open", "module", "declaration", "source_path", "source_blob")
    with (output / "theorem-map.csv").open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        writer.writerows(csv_rows)
    validate_supporting_evidence(kit, revision, data, draft)
    files = [p for p in kit.rglob("*") if p.is_file() and p != kit / "manifest.json"
             and not any(x in {"__pycache__", "tmp"} for x in p.relative_to(kit).parts)]
    pending_line_endings = [path.relative_to(kit).as_posix() for path in files
                           if path.suffix.lower() not in {".pdf", ".png", ".zip"} and b"\r\n" in path.read_bytes()]
    require(draft or not pending_line_endings,
            f"Write new text artifacts with physical LF before final hashing: {pending_line_endings}")
    environment = {"python": sys.version, "platform": platform.platform(),
                   "git": git(root, "--version").decode().strip(),
                   "lean_toolchain": blob(root, revision, "lean-toolchain").decode().strip(),
                   "mathlib_revision": next(p["rev"] for p in json.loads(blob(root, revision, "lake-manifest.json"))["packages"] if p["name"] == "mathlib"),
                   "packages": {p: importlib.metadata.version(p) for p in ("reportlab", "matplotlib", "pypdf")}}
    manifest = {"schema_version": 1, "version": data["version"], "title": data["title"], "date": data["date"],
                "mode": "draft" if draft else "final", "selected_source_sha": revision,
                "accepted_source_sha": None if draft else revision, "baseline_sha": BASELINE,
                "manuscript_sha256": manuscript_hash,
                "acceptance_evidence_sha256": digest(evidence_path.read_bytes()) if evidence_path.exists() else None,
                "pending_claim_statuses": pending, "pending_provider_lookups": missing,
                "pending_line_endings": pending_line_endings,
                "environment": environment, "protected_files": protected,
                "artifact_files": {p.relative_to(kit).as_posix(): digest(p.read_bytes()) for p in sorted(files)},
                "self_excluded": ["manifest.json"]}
    (kit / "manifest.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n")
    verify(kit, allow_draft=draft)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--draft", action="store_true", help="Produce a conspicuously labelled draft; never accepted evidence")
    parser.add_argument("--source", help="Full immutable research commit; final must match acceptance evidence")
    args = parser.parse_args()
    try:
        build(Path(__file__).resolve().parent, args.draft, args.source)
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"Release build FAILED: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

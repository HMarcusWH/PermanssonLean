"""Verify the separately versioned research companion without modifying old artifacts."""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import re
import subprocess
import sys
import zipfile
from pathlib import Path

BASELINE = "6191a1acbf00867042a21c8e6c4a532af43017bc"
FINAL_STATUSES = {"PROVED", "DEFINED", "OPEN", "REFUTED", "COUNTEREXAMPLE",
                  "REUSED", "ASSUMED", "COMPUTATIONAL", "DERIVED",
                  "ACCEPTED_PROVIDER", "FROZEN_PROVIDER"}
ANCHORS = {"C69", "C70", "E1", "F1", "A3", "D2", "X1"}
PR_NUMBERS = {"C69": 69, "C70": 70, "E1": 71, "F1": 72, "A3": 73, "D2": 74, "X1": 75}
REQUIRED_FOCUSED = {
    "C69": {"C-Exit D unconditional restart focused smoke"},
    "C70": {"C-Exit D unconditional restart focused smoke", "C-Exit E random-entry occupation focused smoke"},
    "E1": {"C-Exit D unconditional restart focused smoke", "C-Exit E random-entry occupation focused smoke", "E1 approximate-quotient focused smoke"},
    "F1": {"F1 multi-agent protocols focused smoke"},
    "A3": {"A3 contractive robustness focused smoke", "E1 approximate-quotient focused smoke"},
    "D2": {"D2 finite residence focused smoke"},
    "X1": {"X1 exact commons focused smoke"},
}
SHA = re.compile(r"^[0-9a-f]{40}$")
APPROVED_MANUSCRIPT_SHA256 = "8022291f1ec19961578bdcb60f205fdec31057982bf9a78f6b9610bd3b184239"
APPROVED_MANUSCRIPT_SEMANTIC_SHA256 = "45c7c572314448ceda52bd167c3ac2cb2a69d3853b35fd13dad10a2fdf3cab4a"
APPROVED_BOUNDARIES_SHA256 = "780fb3ec0d45f97d2e48dcbd55825a6cd7cc3b10fbd4340b7d42c587ed663685"
REVIEWED_CODE_FILES = {"build_release.py", "verify_release.py", "package_release.py", "c10_archive_validation.py"}
REQUIRED_CLAIM_STATUSES = {
    "R.SCOPE": "DEFINED", "CORE.IDENTITY": "FROZEN_PROVIDER",
    "C69.RESTART": "ACCEPTED_PROVIDER", "C70.SWITCH": "ACCEPTED_PROVIDER",
    "A2.FINITE": "ACCEPTED_PROVIDER", "E1.LINEAR": "ACCEPTED_PROVIDER",
    "B2.SEQUENTIAL": "ACCEPTED_PROVIDER", "F1.PROTOCOL": "ACCEPTED_PROVIDER",
    "F1.MA2": "OPEN", "A3.DUAL": "PROVED", "A3.SURVIVAL": "PROVED",
    "D2.RESIDENCE": "PROVED", "D2.ORDER": "PROVED", "X1.MODEL": "PROVED",
    "X1.NOEXACT": "PROVED", "X1.OCCUPATION": "PROVED", "X1.FINITEOUTPUT": "PROVED",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def semantic_digest(data):
    return digest(json.dumps(data, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8"))


def git(root, *args):
    proc = subprocess.run(["git", "-C", str(root), *args], capture_output=True)
    require(proc.returncode == 0,
            f"git {' '.join(args)} failed: {proc.stderr.decode('utf-8', 'replace')}")
    return proc.stdout


def blob(root, revision, path):
    return git(root, "show", f"{revision}:{path}")


def tree(root, revision):
    result = {}
    for record in git(root, "ls-tree", "-rz", "--full-tree", revision).split(b"\0"):
        if record:
            header, path = record.split(b"\t", 1)
            mode, kind, oid = header.decode().split()
            require(kind == "blob", f"Unexpected non-blob source entry: {path!r}")
            result[path.decode("utf-8")] = {"mode": mode, "git_blob_sha1": oid}
    return result


def protected_snapshot(root, revision):
    """Git blobs, never Windows working-file bytes, define historical preservation."""
    base = tree(root, BASELINE)
    fixed = {"PermanssonLean.lean", "lean-toolchain", "lake-manifest.json", "lakefile.toml",
             "CITATION.cff", "docs/PAPER_VERIFICATION_MANIFEST.md", "docs/releases/v0.1.8.json"}
    whole_prefixes = ("PermanssonLean/", "paper/", "provenance/", "application/",
                      "verification/destructive/", "verification/v0.1.8_release_gate/", "verification/lean/")

    def baseline_solver(path):
        name = Path(path).name
        return (path.startswith("PermanssonResearch/ReverseSolver/") or
                (path.startswith("docs/") and name.startswith(("D0_", "D1_"))) or
                (path.startswith("verification/research/") and
                 name.startswith(("d0_", "test_d0_", "test_d1_", "test_history_",
                                  "test_nonstationary_", "test_bellman_", "test_controlled_",
                                  "c10_", "test_lane_c10"))))

    protected = {p for p in base if p in fixed or p.startswith(whole_prefixes) or baseline_solver(p)}
    for label, selected in (("selected research cut", revision), ("current release HEAD", "HEAD")):
        current = tree(root, selected)
        unexpected = {p for p in current if p not in base and (p in fixed or p.startswith(whole_prefixes))}
        require(not unexpected, f"{label}: new files inside frozen trees: {sorted(unexpected)}")
        changed = [p for p in sorted(protected) if current.get(p) != base[p]]
        require(not changed, f"{label}: historical protected blobs differ from {BASELINE}: {changed}")
    ordered = sorted(protected)
    proc = subprocess.run(["git", "-C", str(root), "cat-file", "--batch"],
                          input="".join(base[p]["git_blob_sha1"] + "\n" for p in ordered).encode(),
                          capture_output=True)
    require(proc.returncode == 0, "Cannot read canonical protected blobs")
    result, cursor = [], 0
    for path in ordered:
        end = proc.stdout.index(b"\n", cursor)
        oid, kind, size = proc.stdout[cursor:end].decode().split()
        require(oid == base[path]["git_blob_sha1"] and kind == "blob", "Git batch blob order mismatch")
        size = int(size)
        payload = proc.stdout[end + 1:end + 1 + size]
        result.append({"path": path, **base[path], "sha256": digest(payload)})
        cursor = end + size + 2
    require(cursor == len(proc.stdout), "Unexpected Git blob payload")
    return result


def strings(value, field):
    if value is None or value is False:
        return []
    if isinstance(value, str):
        return [value] if value else []
    require(isinstance(value, list) and all(isinstance(x, str) for x in value),
            f"{field} must be a string or a list of strings")
    return value


def validate_manuscript(data, draft, source_bytes=None):
    for key in ("title", "subtitle", "author", "date", "version", "abstract"):
        require(isinstance(data.get(key), str), f"Manuscript {key} must be a string")
    require(data["version"] == "0.2.0" or (draft and data["version"] == "0.2.0-research-draft"),
            "Final kit version must be 0.2.0; the research-draft suffix is draft-only")
    require(isinstance(data.get("sections"), list) and data["sections"], "No manuscript sections")
    anchors, pending = set(), []
    for section in data["sections"]:
        require(isinstance(section.get("title"), str), "Section title missing")
        strings(section.get("paragraphs", []), "paragraphs")
        require(isinstance(section.get("claims", []), list), "claims must be a list")
        for eq in section.get("equations", []):
            require(isinstance(eq.get("latex"), str) and isinstance(eq.get("caption", ""), str),
                    "Equation latex/caption must be strings")
        for claim in section.get("claims", []):
            for key in ("anchor", "title", "status", "statement"):
                require(isinstance(claim.get(key), str) and claim[key], f"Claim {key} missing")
            require(claim["anchor"] not in anchors, f"Duplicate claim anchor {claim['anchor']}")
            anchors.add(claim["anchor"])
            status = claim["status"].upper()
            if status not in FINAL_STATUSES:
                pending.append(f"{claim['anchor']}: {claim['status']}")
            for key in ("assumptions", "proof", "open"):
                strings(claim.get(key, []), key)
            require(isinstance(claim.get("providers", []), list), "providers must be a list")
            if status in {"PROVED", "REUSED", "DERIVED", "REFUTED", "COUNTEREXAMPLE",
                          "ACCEPTED_PROVIDER", "FROZEN_PROVIDER"}:
                require(claim.get("providers"), f"{claim['anchor']} needs exact source providers")
            if status == "OPEN":
                require(strings(claim.get("open", []), "open"), f"{claim['anchor']} must state its open boundary")
            for provider in claim.get("providers", []):
                require(all(isinstance(provider.get(k), str) and provider[k]
                            for k in ("module", "declaration")), "Incomplete source provider")
    require(draft or not pending, f"Pending/unknown claim statuses require --draft: {pending}")
    if not draft:
        statuses = {claim["anchor"]: claim["status"] for section in data["sections"] for claim in section.get("claims", [])}
        require(statuses == REQUIRED_CLAIM_STATUSES,
                "Final manuscript must retain the exact 17 reviewed anchors/statuses, including OPEN F1.MA2")
        require(semantic_digest(data) == APPROVED_MANUSCRIPT_SEMANTIC_SHA256,
                "Final scientific contract differs from the reviewed manuscript; statements, assumptions, proofs and OPEN boundaries are frozen")
        if source_bytes is not None:
            require(digest(source_bytes) == APPROVED_MANUSCRIPT_SHA256,
                    "Final manuscript bytes differ from the reviewed source")
    return pending


def lean_declarations(source):
    """Conservative namespace-aware source lookup; CI remains the elaboration evidence."""
    cleaned, i, depth, quoted = [], 0, 0, False
    while i < len(source):
        pair = source[i:i+2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                cleaned.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif quoted:
            if source[i] == "\\":
                cleaned.extend("  ")
                i += 2
            else:
                quoted = source[i] != '"'
                cleaned.append(" ")
                i += 1
        elif pair == "/-":
            depth = 1
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            quoted = True
            cleaned.append(" ")
            i += 1
        else:
            cleaned.append(source[i])
            i += 1
    scopes, names = [], set()
    decl = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|unsafe)\s+)*"
                      r"(?:theorem|lemma|def|abbrev|structure|class|inductive|opaque|instance)\s+([^\s:({\[]+)")
    for raw in "".join(cleaned).splitlines():
        line = raw.strip()
        if match := re.match(r"namespace\s+(\S+)", line):
            scopes.append(("namespace", match[1]))
        elif match := re.match(r"(?:noncomputable\s+)?section(?:\s+(\S+))?$", line):
            scopes.append(("section", match[1] or ""))
        elif re.match(r"end(?:\s+\S+)?$", line):
            if scopes:
                scopes.pop()
        elif match := decl.match(line):
            name = match[1]
            prefix = ".".join(n for kind, n in scopes if kind == "namespace")
            names.add(name.removeprefix("_root_.") if name.startswith("_root_.")
                      else ".".join(x for x in (prefix, name) if x))
    return names


def source_providers(root, revision, manuscript, draft):
    paths, records, pending = tree(root, revision), [], []
    cache = {}
    for section in manuscript["sections"]:
        for claim in section.get("claims", []):
            row = {"section": section["title"], **claim, "source_providers": []}
            for provider in claim.get("providers", []):
                module, declaration = provider["module"], provider["declaration"]
                require(re.fullmatch(r"[A-Za-z0-9_'.]+", module), f"Invalid module {module}")
                path = module.replace(".", "/") + ".lean"
                if path not in cache:
                    cache[path] = lean_declarations(blob(root, revision, path).decode("utf-8")) if path in paths else set()
                found = declaration in cache[path]
                if not found:
                    pending.append(f"{claim['anchor']}: {declaration} absent in {revision}:{path}")
                row["source_providers"].append({**provider, "source_path": path,
                    "source_blob": paths.get(path, {}).get("git_blob_sha1"), "found": found})
            records.append(row)
    require(draft or not pending, "Provider lookup failed: " + "; ".join(pending))
    return records, pending


def validate_acceptance(root, evidence, revision, draft, manuscript=None):
    if draft:
        return []
    require(evidence is not None, "Final build requires acceptance-evidence.json")
    require(evidence.get("schema_version") == 1, "Unsupported acceptance schema")
    require(evidence.get("repository") == "HMarcusWH/PermanssonLean", "Wrong evidence repository")
    require(evidence.get("baseline_sha") == BASELINE, "Wrong preservation baseline")
    require(evidence.get("accepted_source_sha") == revision, "Evidence/source revision mismatch")
    require(evidence.get("acceptance_status") in {"accepted", "pass"}, "Research source acceptance is pending")
    require(semantic_digest(evidence.get("open_boundaries")) == APPROVED_BOUNDARIES_SHA256,
            "Accepted evidence must retain all eight reviewed scientific OPEN boundaries")
    receipts = evidence.get("receipts", [])
    require({r.get("anchor") for r in receipts} == ANCHORS and len(receipts) == len(ANCHORS),
            "Need one exact accepted receipt for each C69/C70/E1/F1/A3/D2/X1 anchor")
    x1 = next(receipt for receipt in receipts if receipt["anchor"] == "X1")
    require(git(root, "rev-parse", revision + "^{tree}") ==
            git(root, "rev-parse", x1["synthetic_merge_sha"] + "^{tree}"),
            "Final selected source tree differs from the final X1 checked synthetic tree")
    for receipt in receipts:
        label = receipt["anchor"]
        require(receipt.get("pr") == PR_NUMBERS[label], f"{label}: receipt belongs to a different PR")
        require(receipt.get("acceptance_status") in {"accepted", "pass"}, f"{label}: acceptance is pending")
        for key in ("source_sha", "base_sha", "synthetic_merge_sha", "main_merge_sha"):
            require(SHA.fullmatch(receipt.get(key, "")), f"{label}: invalid {key}")
        parents = git(root, "show", "-s", "--format=%P", receipt["synthetic_merge_sha"]).decode().split()
        require(parents == [receipt["base_sha"], receipt["source_sha"]], f"{label}: synthetic merge parents mismatch")
        main_parents = git(root, "show", "-s", "--format=%P", receipt["main_merge_sha"]).decode().split()
        require(main_parents == [receipt["base_sha"], receipt["source_sha"]], f"{label}: main merge parents mismatch")
        require(git(root, "rev-parse", receipt["main_merge_sha"] + "^{tree}") ==
                git(root, "rev-parse", receipt["synthetic_merge_sha"] + "^{tree}"),
                f"{label}: main merge tree differs from checked synthetic tree")
        require(subprocess.run(["git", "-C", str(root), "merge-base", "--is-ancestor",
                                receipt["main_merge_sha"], revision], capture_output=True).returncode == 0,
                f"{label}: recorded main merge is not in accepted source ancestry")
        require(subprocess.run(["git", "-C", str(root), "merge-base", "--is-ancestor",
                                receipt["source_sha"], revision], capture_output=True).returncode == 0,
                f"{label}: accepted source does not contain provider head")
        require(receipt.get("open_findings") == [], f"{label}: unresolved acceptance findings")
        c10 = receipt.get("c10", {})
        require(c10.get("status") == "pass" and c10.get("source_head_sha") == receipt["source_sha"]
                and str(c10.get("logs_url", "")).startswith("https://github.com/"), f"{label}: C10 receipt missing/misbound")
        counts = receipt.get("counts", {})
        require(all(isinstance(counts.get(k), int) and counts[k] > 0
                    for k in ("declarations", "tests", "imports")), f"{label}: missing verified counts")
        review = receipt.get("review", {})
        require(review.get("status") in {"pass", "approved", "no_findings"}
                and review.get("commit_sha") == receipt["source_sha"]
                and str(review.get("url", "")).startswith("https://github.com/"), f"{label}: exact-head review missing")
        runs = receipt.get("workflow_runs", [])
        require(len(runs) >= 5 and all(isinstance(r.get("run_id"), int)
                and r.get("conclusion") == "success" and r.get("head_sha") == receipt["source_sha"]
                for r in runs), f"{label}: workflows incomplete or misbound")
        names = {r.get("name", "") for r in runs}
        required = {"Lean", "Research Lean", "Executable verification", "Application contract"} | REQUIRED_FOCUSED[label]
        require(required <= names, f"{label}: required workflows missing: {sorted(required - names)}")
        require(any(r.get("name") == "Research Lean" and r["run_id"] == receipt.get("research_run_id")
                    and r.get("checked_sha") == receipt["synthetic_merge_sha"]
                    for r in runs), f"{label}: Research run identifier mismatch")
        app = next(r for r in runs if r.get("name") == "Application contract")
        jobs = app.get("jobs", [])
        require(all(j.get("conclusion") == "success" for j in jobs)
                and any("ubuntu" in j.get("name", "").lower() for j in jobs)
                and any("windows" in j.get("name", "").lower() for j in jobs), f"{label}: both application OS jobs required")
    require(manuscript is not None, "Final acceptance requires the manuscript provider inventory")
    source_providers(root, x1["source_sha"], manuscript, draft=False)
    return receipts


def validate_c10_archives(kit, root, evidence, draft):
    origins_path = kit / "evidence/c10/artifact-origins.json"
    if not origins_path.exists():
        require(draft, "Final kit needs preserved C10 machine receipts")
        return
    origins = json.loads(origins_path.read_text(encoding="utf-8"))
    require(origins.get("schema_version") == 1, "Unknown C10 archive-origin schema")
    rows = origins.get("artifacts", [])
    receipts = {row["anchor"]: row for row in (evidence or {}).get("receipts", [])}
    require(len(rows) == len({row.get("anchor") for row in rows}), "Duplicate C10 archive anchors")
    require({row.get("anchor") for row in rows} == (set(receipts) if draft else ANCHORS),
            "C10 archive anchors do not match accepted receipt inventory")
    for origin in rows:
        anchor = origin["anchor"]
        receipt = receipts[anchor]
        require(origin.get("repository") == "HMarcusWH/PermanssonLean"
                and origin.get("source_sha") == receipt["source_sha"]
                and origin.get("run_id") == receipt["research_run_id"]
                and isinstance(origin.get("artifact_id"), int) and origin["artifact_id"] > 0,
                f"{anchor}: C10 publisher origin is misbound")
        relative = origin.get("path", "")
        archive = kit / relative
        require(relative.startswith("evidence/c10/") and archive.suffix == ".zip"
                and archive.resolve().is_relative_to(kit.resolve()), f"{anchor}: invalid C10 archive path")
        require(re.fullmatch(r"[0-9a-f]{64}", origin.get("sha256", ""))
                and digest(archive.read_bytes()) == origin["sha256"], f"{anchor}: C10 publisher ZIP digest mismatch")
        with zipfile.ZipFile(archive) as zipped:
            names = zipped.namelist()
            require(len(names) == len(set(names)) and "evidence_manifest.json" in names,
                    f"{anchor}: duplicate/missing C10 ZIP entries")
            machine = json.loads(zipped.read("evidence_manifest.json"))
            require(machine.get("format") == "Permansson.C10.release-evidence.v2", f"{anchor}: wrong C10 format")
            artifacts = machine.get("artifacts", {})
            require(isinstance(artifacts, dict) and set(names) == {"evidence_manifest.json", *artifacts},
                    f"{anchor}: C10 ZIP entry inventory mismatch")
            require(all(not Path(name).is_absolute() and ".." not in Path(name).parts for name in names),
                    f"{anchor}: unsafe C10 ZIP entry")
            for name, expected in artifacts.items():
                require(digest(zipped.read(name)) == expected, f"{anchor}: C10 nested artifact digest mismatch: {name}")
            expected_source = {"repository": "HMarcusWH/PermanssonLean", "pr_number": receipt["pr"],
                               "head_sha": receipt["source_sha"], "base_sha": receipt["base_sha"],
                               "synthetic_merge_sha": receipt["synthetic_merge_sha"]}
            require(machine.get("source") == expected_source, f"{anchor}: C10 machine source binding mismatch")
            specification = machine.get("specification", {})
            path = specification.get("path", "")
            require(path and not Path(path).is_absolute() and ".." not in Path(path).parts,
                    f"{anchor}: invalid C10 specification path")
            require(digest(blob(root, receipt["source_sha"], path)) == specification.get("sha256"),
                    f"{anchor}: C10 specification differs from canonical source blob")
        from c10_archive_validation import validate_c10_archive
        validate_c10_archive(archive, expected_source, root)


def validate_supporting_evidence(kit, revision, manuscript, draft):
    """Bind captured external validation to the exact shipped inputs and reviewed code."""
    if draft:
        return
    from pypdf import PdfReader
    for name in ("compile-evidence.json", "review-evidence.json"):
        require((kit / name).is_file(), f"Final kit requires {name}")
    compilation = json.loads((kit / "compile-evidence.json").read_text(encoding="utf-8"))
    review = json.loads((kit / "review-evidence.json").read_text(encoding="utf-8"))
    for name, receipt in (("compile", compilation), ("review", review)):
        require(receipt.get("schema_version") == 1 and receipt.get("research_source_sha") == revision,
                f"{name} evidence source/schema mismatch")
    manuscript_hash = digest((kit / "manuscript.json").read_bytes())
    tex_hash = digest((kit / "output/pdf/Permansson_Research_Companion_v0.2.0.tex").read_bytes())
    pdf_path = kit / "output/pdf/Permansson_Research_Companion_v0.2.0.pdf"
    require(compilation.get("manuscript_json_sha256") == manuscript_hash
            and compilation.get("tex_sha256") == tex_hash, "Compile evidence manuscript/TeX hash mismatch")
    primary = compilation.get("primary_pdf", {})
    require(primary.get("sha256") == digest(pdf_path.read_bytes())
            and primary.get("pages") == len(PdfReader(pdf_path).pages)
            and str(primary.get("visual_review", "")).startswith("PASS:"),
            "Compile evidence primary PDF hash/pages/visual result mismatch")
    desktop = compilation.get("desktop_tex_compiler", {})
    require(desktop.get("tool") == "Codex compile_latex_document"
            and desktop.get("result") == "success" and desktop.get("input_sha256") == tex_hash,
            "Desktop compile evidence is unsuccessful or bound to different TeX")
    independent = compilation.get("independent_tex_compiler", {})
    provider_count = sum(len(claim.get("providers", [])) for section in manuscript["sections"]
                         for claim in section.get("claims", []))
    require(independent.get("exit_code") == 0 and independent.get("input_sha256") == tex_hash
            and independent.get("archive_checksum_verified") is True
            and re.fullmatch(r"[0-9a-f]{64}", independent.get("official_archive_sha256", ""))
            and re.fullmatch(r"[0-9a-f]{64}", independent.get("diagnostic_pdf_sha256", ""))
            and independent.get("overfull_hboxes") == 0 and independent.get("underfull_boxes") == 0
            and independent.get("provider_identifiers_present") == provider_count
            and independent.get("provider_identifiers_missing") == []
            and independent.get("repository_url_present") is True
            and independent.get("accepted_snapshot_present") is True
            and independent.get("draft_banner_present") is False
            and str(independent.get("visual_review", "")).startswith("PASS:"),
            "Independent compile/visual evidence is incomplete or bound to different TeX")
    require(review.get("open_acceptance_findings") == [], "Review evidence has unresolved acceptance findings")
    code = review.get("reviewed_code_sha256", {})
    require(set(code) == REVIEWED_CODE_FILES, "Review evidence must cover every required release validator/exporter")
    for name, expected in code.items():
        require((kit / name).is_file() and digest((kit / name).read_bytes()) == expected,
                f"Reviewed code hash mismatch: {name}")


def tex_escape(text):
    mapping = {"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$",
               "#": r"\#", "_": r"\_", "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}",
               "^": r"\textasciicircum{}"}
    result = []
    for token in re.split(r"(\s+)", text):
        for index, char in enumerate(token):
            result.append(mapping.get(char, char))
            if not token.isspace() and len(token) >= 25 and (index + 1) % 12 == 0 and index + 1 < len(token):
                result.append(r"\allowbreak{}")
    return "".join(result)


def plain(text):
    return str(text).translate(str.maketrans({"\u2010": "-", "\u2011": "-", "\u2012": "-",
                                             "\u2013": "-", "\u2014": "-", "\u2212": "-"}))


def narrative_strings(data):
    yield data["title"]
    yield data["subtitle"]
    yield data["author"]
    yield data["date"]
    yield data["abstract"]
    for section in data["sections"]:
        yield section["title"]
        yield from strings(section.get("paragraphs", []), "paragraphs")
        for eq in section.get("equations", []):
            if eq.get("caption"):
                yield eq["caption"]
        for claim in section.get("claims", []):
            yield claim["anchor"]
            yield claim["title"]
            yield claim["statement"]
            for key in ("assumptions", "proof", "open"):
                yield from strings(claim.get(key, []), key)
            for provider in claim.get("providers", []):
                yield provider["module"]
                yield provider["declaration"]


def verify(kit, allow_draft=False):
    from pypdf import PdfReader
    root = Path(git(kit, "rev-parse", "--show-toplevel").decode().strip())
    manifest = json.loads((kit / "manifest.json").read_text(encoding="utf-8"))
    require(manifest.get("mode") in {"draft", "final"}, "Unknown release mode")
    draft = manifest.get("mode") == "draft"
    require(allow_draft or not draft, "Draft artifact requires --allow-draft; it is not an accepted release")
    data = json.loads((kit / "manuscript.json").read_text(encoding="utf-8"))
    validate_manuscript(data, draft, (kit / "manuscript.json").read_bytes())
    revision = manifest["selected_source_sha"]
    require(SHA.fullmatch(revision), "Invalid source revision")
    require(manifest.get("schema_version") == 1 and manifest.get("baseline_sha") == BASELINE, "Manifest schema/baseline mismatch")
    require(manifest.get("version") == data["version"] and manifest.get("title") == data["title"]
            and manifest.get("date") == data["date"], "Manifest/manuscript metadata mismatch")
    evidence = json.loads((kit / "acceptance-evidence.json").read_text(encoding="utf-8")) if (kit / "acceptance-evidence.json").exists() else None
    validate_acceptance(root, evidence, revision, draft, data)
    validate_c10_archives(kit, root, evidence, draft)
    require(manifest.get("accepted_source_sha") == (None if draft else revision), "Acceptance mode mismatch")
    if not draft:
        require(not any(manifest.get(key) for key in
                        ("pending_claim_statuses", "pending_provider_lookups", "pending_line_endings")),
                "Final manifest contains pending obligations")
    require(manifest.get("self_excluded") == ["manifest.json"], "Unexpected self-hash exclusions")
    environment = manifest.get("environment", {})
    expected_mathlib = next(package["rev"] for package in json.loads(blob(root, revision, "lake-manifest.json"))["packages"]
                            if package["name"] == "mathlib")
    require(environment.get("lean_toolchain") == blob(root, revision, "lean-toolchain").decode().strip()
            and environment.get("mathlib_revision") == expected_mathlib, "Recorded Lean/mathlib pins differ from accepted source")
    require(manifest["protected_files"] == protected_snapshot(root, revision), "Protected canonical-blob manifest mismatch")
    artifacts = manifest["artifact_files"]
    require("manifest.json" not in artifacts, "Manifest may not hash itself")
    on_disk = {p.relative_to(kit).as_posix() for p in kit.rglob("*") if p.is_file()
               and p != kit / "manifest.json" and not any(x in {"tmp", "__pycache__"} for x in p.relative_to(kit).parts)}
    require(set(artifacts) == on_disk, "Manifest must inventory every new kit file")
    for relative, expected in artifacts.items():
        path = kit / relative
        require(path.resolve().is_relative_to(kit.resolve()), f"Artifact path escapes kit: {relative}")
        require(path.is_file() and digest(path.read_bytes()) == expected, f"Artifact hash mismatch: {relative}")
    required = {"manuscript.json", "build_release.py", "verify_release.py", "README.md",
                "output/pdf/Permansson_Research_Companion_v0.2.0.tex",
                "output/pdf/Permansson_Research_Companion_v0.2.0.pdf",
                "output/pdf/theorem-map.json", "output/pdf/theorem-map.csv"}
    if not draft:
        required |= {"acceptance-evidence.json", "compile-evidence.json", "review-evidence.json",
                     "test_c10_archive_validation.py", "test_release_guards.py"} | REVIEWED_CODE_FILES
    require(required <= artifacts.keys(), "Manifest omitted required new artifacts")
    validate_supporting_evidence(kit, revision, data, draft)
    manuscript_hash = digest((kit / "manuscript.json").read_bytes())
    require(manifest["manuscript_sha256"] == manuscript_hash, "Manuscript digest mismatch")
    require(manifest.get("acceptance_evidence_sha256") ==
            (digest((kit / "acceptance-evidence.json").read_bytes()) if evidence is not None else None),
            "Acceptance evidence digest mismatch")
    expected_rows, _ = source_providers(root, revision, data, draft)
    maps = json.loads((kit / "output/pdf/theorem-map.json").read_text(encoding="utf-8"))
    require(maps == {"version": data["version"], "source_sha": revision, "claims": expected_rows}, "Full theorem-map/source mismatch")
    expected_csv = []
    for row in expected_rows:
        for provider in row["source_providers"] or [{}]:
            expected_csv.append({key: str(value) for key, value in csv_row(row, provider).items()})
    with (kit / "output/pdf/theorem-map.csv").open(encoding="utf-8", newline="") as stream:
        require(list(csv.DictReader(stream)) == expected_csv, "CSV theorem map lost assumptions/providers")
    tex = (kit / "output/pdf/Permansson_Research_Companion_v0.2.0.tex").read_text(encoding="utf-8")
    for marker in (f"% Source-SHA: {revision}", f"% Manuscript-SHA256: {manuscript_hash}",
                   f"% Version: {data['version']}", f"% Mode: {'draft' if draft else 'final'}"):
        require(marker in tex, f"TeX metadata missing: {marker}")
    visible_tex = tex.replace(r"\allowbreak{}", "")
    tex_meta = lambda value: tex_escape(plain(value)).replace(r"\allowbreak{}", "")
    require(r"\title{" + tex_meta(data["title"]) + r"\\[5pt]\large " + tex_meta(data["subtitle"]) + "}" in visible_tex,
            "TeX title/subtitle metadata mismatch")
    for command, value in (("author", data["author"]), ("date", data["date"])):
        require("\\" + command + "{" + tex_meta(value) + "}" in visible_tex,
                f"TeX {command} metadata mismatch")
    for value in narrative_strings(data):
        require(tex_escape(plain(value)).replace(r"\allowbreak{}", "") in visible_tex,
                f"TeX omitted narrative: {value[:90]}")
    pdf = PdfReader(kit / "output/pdf/Permansson_Research_Companion_v0.2.0.pdf")
    meta = pdf.metadata
    for key, value in {"/Title": data["title"], "/Author": data["author"], "/Subject": data["subtitle"],
                       "/PermanssonDate": data["date"],
                       "/PermanssonSourceSHA": revision, "/PermanssonManuscriptSHA256": manuscript_hash,
                       "/PermanssonVersion": data["version"], "/PermanssonMode": "draft" if draft else "final"}.items():
        require(meta.get(key) == value, f"PDF metadata mismatch: {key}")
    normalize = lambda s: re.sub(r"\s+", "", plain(s)).replace("\u200b", "")
    pages = []
    for number, page in enumerate(pdf.pages, 1):
        extracted = page.extract_text() or ""
        footer = "Permansson | Research companion v0.2.0" + (" | DRAFT" if draft else "")
        extracted = extracted.replace(footer + "\n" + str(number) + "\n", "", 1)
        pages.append(extracted)
    text = normalize("\n".join(pages))
    for value in narrative_strings(data):
        require(normalize(value) in text, f"PDF omitted narrative: {value[:90]}")
    print(f"{'DRAFT' if draft else 'FINAL'} kit verification PASS: {len(pdf.pages)} pages, "
          f"{len(expected_rows)} claims, {len(manifest['protected_files'])} protected canonical blobs")


def csv_row(row, provider):
    return {"anchor": row["anchor"], "title": row["title"], "status": row["status"],
            "statement": row["statement"], "assumptions": json.dumps(row.get("assumptions", []), ensure_ascii=False),
            "proof": json.dumps(row.get("proof", []), ensure_ascii=False),
            "open": json.dumps(row.get("open", []), ensure_ascii=False),
            **{key: provider.get(key, "") or "" for key in ("module", "declaration", "source_path", "source_blob")}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--allow-draft", action="store_true")
    args = parser.parse_args()
    try:
        verify(Path(__file__).resolve().parent, args.allow_draft)
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"Release verification FAILED: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())

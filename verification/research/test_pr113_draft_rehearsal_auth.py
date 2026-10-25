"""Real-byte equality checks for the unapproved, two-root draft rehearsal."""
import io
import json
import hashlib
import unittest
import zipfile

import pr113_draft_rehearsal_auth as r

H="a"*40

def digest(raw):return hashlib.sha256(raw).hexdigest()

def zipped(raw):
    out=io.BytesIO()
    with zipfile.ZipFile(out,"w",zipfile.ZIP_DEFLATED) as z:
        for key,val in sorted(raw.items()):
            z.writestr(key,val)
    return out.getvalue()

def fixture():
    pdf=b"%PDF-1.4\nexample draft bytes"
    tex=b"\\documentclass{article}\n"
    render=b"PNG-RENDER"
    sources={r.PREFIX+p:digest(p.encode()) for p in r.SOURCE_PATHS}
    sourcebytes={p:p.encode() for p in r.SOURCE_PATHS}
    manifest={
        "format":"Permansson.MathClosure.BuildReceipt.v1",
        "status":"DRAFT_NOT_ACCEPTED",
        "source_commit_sha":H,
        "independent_review":"NOT_RECEIVED",
        "visual_inspection":"NOT_PERFORMED",
        "source_ci_validation":"NOT_BOUND_TO_MERGED_MAIN",
        "source_tree_files":sources,
        "pdf_page_count":1,
        "pdf_sha256":digest(pdf),
        "tex_sha256":digest(tex),
        "latex_log_sha256":digest(b"compiler-log"),
    }
    manifest_raw=(json.dumps(manifest,sort_keys=True)+"\n").encode()
    review={"status":"MISSING_POST_MERGE_SOURCE_AND_REVIEWS",
            "ci_receipts":[],"independent_reviews":[]}
    review_raw=(json.dumps(review,sort_keys=True)+"\n").encode()
    nested=zipped({
        "manuscript/"+p:sourcebytes[p] for p in r.SOURCE_PATHS
    }|{
        "manifest.lock.json":manifest_raw,
        "Permansson_Mathematical_Closure.pdf":pdf,
        "source_ci_receipts.lock.json":review_raw,
    })
    body={
       "Permansson_Mathematical_Closure.pdf":pdf,
       "Permansson_Mathematical_Closure.tex":tex,
       "Permansson_Mathematical_Closure_E2E.zip":nested,
       "manifest.lock.json":manifest_raw,
       "source_ci_receipts.lock.json":review_raw,
       "latex_build.log":b"compiler-log",
    }
    sums=(
        "".join(digest(body[k])+"  "+k+"\n" for k in (
            "Permansson_Mathematical_Closure.pdf",
            "Permansson_Mathematical_Closure.tex",
            "manifest.lock.json","source_ci_receipts.lock.json",
            "Permansson_Mathematical_Closure_E2E.zip"))
    ).encode()
    body["SHA256SUMS.txt"]=sums
    outer={}
    for side in ("first","second"):
        for key,value in body.items():
            outer[side+"/"+key]=value
        outer[side+"/pages/page-1.png"]=render
    report={
       "format":"Permansson.TwoCleanSourceRebuilds.v1",
       "status":"REPRODUCIBLE_DRAFT_ONLY",
       "source_commit_sha":H,
       "source_tree_sha":"b"*40,
       "independent_source_roots":2,
       "two_complete_archive_audits":True,
       "rendered_pages":True,
       "authenticated_ci_artifact":False,
       "scientific_release_approved":False,
       "pdf_sha256":digest(pdf),
       "archive_sha256":digest(nested),
       "manifest_sha256":digest(manifest_raw),
       "byte_comparison":{
           "status":"REPRODUCIBLE_DRAFT_ONLY",
           "source_commit_sha":H,
           "pdf_sha256":digest(pdf),
           "zip_sha256":digest(nested),
           "page_count":1,
       },
    }
    ci={
        "format":"Permansson.CICleanRebuildCandidate.v1",
        "status":"EXECUTED_DRAFT_ONLY_NO_SCHOLARLY_REVIEW",
        "source_head":H,
        "github_repository":"HMarcusWH/PermanssonLean",
        "github_job":"clean-paper-rebuild",
        "github_run_id":100,
        "github_run_attempt":1,
        "pdf_sha256":digest(pdf),
        "archive_sha256":digest(nested),
        "authenticated_ci_artifact":False,
        "scientific_release_approved":False,
    }
    outer["reproduction_receipt.json"]=json.dumps(report).encode()
    outer["ci_execution_identity.json"]=json.dumps(ci).encode()
    return outer

class DraftByteRehearsalTests(unittest.TestCase):
    def test_full_synthetic_two_root_rehearsal_remains_unapproved(self):
        checked=r.audit(zipped(fixture()),H)
        self.assertEqual(checked["source_member_count"],13)
        self.assertEqual(checked["rendered_pages_verified"],1)
        self.assertFalse(checked["actual_GitHub_artifact_authentication"])
        self.assertFalse(checked["mathematical_acceptance"])
        self.assertFalse(checked["publication_authorized"])

    def test_wrong_head_or_changed_actual_pdf_fails(self):
        with self.assertRaises(r.DraftRehearsalError):
            r.audit(zipped(fixture()),"c"*40)
        data=fixture()
        data["second/Permansson_Mathematical_Closure.pdf"]=b"%PDF-1.4\nchanged"
        with self.assertRaises(r.DraftRehearsalError):
            r.audit(zipped(data),H)

    def test_missing_page_and_false_approval_are_rejected(self):
        data=fixture()
        del data["first/pages/page-1.png"]
        with self.assertRaises(r.DraftRehearsalError):
            r.audit(zipped(data),H)
        data=fixture()
        report=json.loads(data["reproduction_receipt.json"])
        report["scientific_release_approved"]=True
        data["reproduction_receipt.json"]=json.dumps(report).encode()
        with self.assertRaises(r.DraftRehearsalError):
            r.audit(zipped(data),H)

    def test_changed_nested_manuscript_source_is_rejected(self):
        data=fixture()
        with zipfile.ZipFile(io.BytesIO(
             data["first/Permansson_Mathematical_Closure_E2E.zip"])) as z:
            rows={name:z.read(name) for name in z.namelist()}
        rows["manuscript/main.tex"]=b"unreviewed new paper source"
        data["first/Permansson_Mathematical_Closure_E2E.zip"]=zipped(rows)
        with self.assertRaises(r.DraftRehearsalError):
            r.audit(zipped(data),H)

if __name__=="__main__":
    unittest.main()

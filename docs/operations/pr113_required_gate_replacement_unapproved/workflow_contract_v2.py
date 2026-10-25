"""VERSIONED T2 reviewed workflow contract CANDIDATE, NOT installed/approved.

The original historical T integrity verifier and its historical 25-file
workflow source remain immutable in T. This successor contract is a distinct
versioned allowlist of the intended exact 30-workflow active configuration.
A SHA-1 Git blob ID is a content commitment, NOT independent authorization.

Install only with an approved atomic workflow+contract+test source change.
"""
from __future__ import annotations
import hashlib
from pathlib import Path
import re
import subprocess
from verification.integrity.reports import HardeningError

FORMAT="Permansson.PR113.VersionedWorkflowContract.v2"
APPROVED_WORKFLOW_BLOBS={
    "a2-smoke.yml": "b1a3c2001614ac873ec015d05d2dfd7e7e04344f",
    "a3-contractive-smoke.yml": "d17cb4a6eecf5083f0eb92dd8437719c752c6e4f",
    "application.yml": "bdd02d48265e08f8cb94b7402da56da9c8e3ec9d",
    "b2-smoke.yml": "c56c37df8f52d1ed09a05b4d81789bca88b0b659",
    "c-exit-random-entry-smoke.yml": "b3523038985e0997177b69578ea77d981e850593",
    "c-exit-restart-d-smoke.yml": "0e5e0028498eaf8802fe5f923b20d38bf62f623b",
    "c-exit-restart-smoke.yml": "e8a2cf304de04e3ccd08edfd0096733a358b6266",
    "c-exit-smoke.yml": "a4a24c40463492998dab761cf06b32ecebb39e0f",
    "c-exit-switch-smoke.yml": "e10e334ed0b3fd327e6c341d851639a5a696accd",
    "d2-residence-smoke.yml": "8bbe39361fea58a7c6717363341f09898d2a94dd",
    "e1-approx-quotient-smoke.yml": "11bba31567059d968133a513c78b9103e43418fc",
    "f1-multiagent-protocols-smoke.yml": "b87a8c082f51f24dd7d533147e676813d1a78b85",
    "lean.yml": "65aa095a9564cbef0bdca035c95b6d8f568d2cf4",
    "pr113-all-case-compiler.yml": "07791f65c6572ca29ada9a8150a643c51958602f",
    "pr113-all-original-semantic-candidates.yml": "2027a05a225dd49e92415bcbd81d73755111d5ef",
    "pr113-clean-paper-rebuild.yml": "a89fdc99e7daa8b418deed2f09898a08677140a8",
    "pr113-compiler-evidence-candidate.yml": "8f762813360a43e344bc328d54d53c2726bf3879",
    "pr113-historical-migration-candidates.yml": "6b62e789eaa40e933faaf350352da386334b49bc",
    "pr113-legacy-semantic-evidence.yml": "6e65891db1239bf87250ff3420e9ea96407353a4",
    "pr113-original-positive-controls-candidate.yml": "16245b42cbfea16ade0cce24bb0c345c2b251a14",
    "pr113-original-semantic-candidates.yml": "ab509cdb5097fb3c1a9e04dbba192adfe304a940",
    "pr113-postseal-replay.yml": "03c5da76dc5c2d5ae40234799294164a4ec46d5c",
    "pr113-preseal-fullscope.yml": "5fb2a30a8b18076cae2fb81210a5d6819d3bab11",
    "pr113-source-controls-v3_1.yml": "0bc958aebde7d56cb2532ac89203522277889322",
    "research-integrity-portability.yml": "380a592039dd9e50b87bb2891771e76b071a2aaa",
    "research-integrity.yml": "54a64e0d2832d965088cf896c1a052d2809b083f",
    "research-lean.yml": "9f5bbfce2da6e4b7a3511b5d360fc9c70c2bd080",
    "research-release-verification.yml": "46ea7ebeae142f794394179154385cf1762b78d3",
    "verification.yml": "c016aa6efcc42e19d81cb148f5db6bc6a439d7d3",
    "x1-commons-smoke.yml": "554966b640d5f4d4ad284f3b5bdd0005c992dd80"
}
REQUIRED_JOBS=frozenset((
    "frozen-source-preservation","release-export-integrity",
    "archive-reproducibility"))
APPROVED_ACTIONS={
    "actions/checkout":"11d5960a326750d5838078e36cf38b85af677262",
    "actions/setup-python":"a26af69be951a213d495a4c3e4e4022e16d87065",
    "actions/upload-artifact":"ea165f8d65b6e75b540449e92b4886f43607fa02",
}
READ_PERMISSIONS=frozenset(("actions","checks","contents","pull-requests"))


def need(ok,msg):
    if not ok:
        raise HardeningError("E_WORKFLOW_CONTRACT",msg)


def git_blob_oid(data):
    return hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()


def load_workflows(root=None):
    """Load real HEAD Git blobs, never checkout shadow or untracked files."""
    root=Path(root).resolve() if root is not None else Path(__file__).resolve().parents[2]
    def git(*args):
        try:
            return subprocess.check_output(["git",*args],cwd=root,
                     stderr=subprocess.DEVNULL,timeout=30)
        except (OSError,subprocess.CalledProcessError,
                subprocess.TimeoutExpired) as exc:
            raise HardeningError("E_WORKFLOW_CONTRACT",
                    "reviewed Git tree not available") from exc
    head=git("rev-parse","HEAD").decode().strip()
    need(re.fullmatch(r"[a-f0-9]{40}",head) is not None,
         "reviewed versioned source HEAD missing")
    entries={}
    for row in git("ls-tree","-r",head,"--",".github/workflows").splitlines():
        try:
            meta,path=row.split(b"\t",1)
            mode,kind,oid=meta.decode().split()
            name=path.decode()
        except (ValueError,UnicodeError) as exc:
            raise HardeningError("E_WORKFLOW_CONTRACT",
                    "unknown workflow Git tree record") from exc
        need(name.startswith(".github/workflows/")
             and "/" not in name.removeprefix(".github/workflows/")
             and name.endswith((".yml",".yaml"))
             and mode=="100644" and kind=="blob"
             and len(oid)==40,
             "unexpected workflow pathname/type/mode")
        label=name.removeprefix(".github/workflows/")
        need(label in APPROVED_WORKFLOW_BLOBS
             and oid==APPROVED_WORKFLOW_BLOBS[label],
             "unreviewed successor Git workflow blob")
        blob=git("show",head+":"+name)
        need(git_blob_oid(blob)==oid,
             "Git blob bytes differ from exact workflow identity")
        entries[label]=blob.decode("utf-8")
    need(set(entries)==set(APPROVED_WORKFLOW_BLOBS),
         "missing or extra reviewed successor workflow")
    return entries


def validate_workflow_set(workflows):
    need(isinstance(workflows,dict) and
         set(workflows)==set(APPROVED_WORKFLOW_BLOBS),
         "entire 30-workflow review set must match exactly")
    for name,oid in APPROVED_WORKFLOW_BLOBS.items():
        text=workflows[name]
        need(isinstance(text,str) and
             git_blob_oid(text.encode("utf-8"))==oid,
             "reviewed source changed: "+name)
        need("pull_request_target" not in text and
             "id-token: write" not in text and
             "contents: write" not in text and
             "actions: write" not in text and
             "pull-requests: write" not in text,
             "workflow source is privileged beyond read-only profile")
        for action,pin in re.findall(
                r"(?m)^\s*- uses:\s*([^@\s]+)@([^\s]+)",text):
            need(re.fullmatch(r"[a-f0-9]{40}",pin) is not None,
                 "workflow action is not full-commit pinned: "+name)
            if action in APPROVED_ACTIONS:
                need(APPROVED_ACTIONS[action]==pin,
                     "workflow action source is not the approved pin")
    research=workflows["research-lean.yml"]
    arch=workflows["research-integrity.yml"]
    need(research.count("\n  research:\n")==1 and
         arch.count("\n  archive-reproducibility:\n")==1 and
         arch.count("\n  frozen-source-preservation:\n")==1 and
         arch.count("\n  release-export-integrity:\n")==1,
         "original required-check job identities changed")
    need("verification.integrity.ci_context" in research and
         "verification.integrity.ci_context" in arch and
         "pr113_historical_artifact_delivery.py" in research and
         "pr113_historical_artifact_delivery.py" in arch and
         "pr113_required_dual_gate.py" in arch and
         "Run research-only exact rational regressions" in research and
         "Generate and independently verify C10" in research and
         "Generate and independently recheck D0" in research and
         "Reject proof placeholders" in research and
         "verification.integrity.run_tests --suite archive" in arch,
         "versioned mandatory historical security and scientific legs missing")
    return {
        "format":FORMAT,"workflows":30,
        "original_historical_unchanged":False,
        "retains_historical_T_and_A2_through_external_original_checkouts":True,
        "original_required_context_names":sorted(REQUIRED_JOBS),
        "mathematical_release_approved":False,
    }


def validate_workflow(text,workflows=None):
    if workflows is None:
        workflows=load_workflows()
    results=validate_workflow_set(workflows)
    need(isinstance(text,str) and
         git_blob_oid(text.encode("utf-8"))==
             APPROVED_WORKFLOW_BLOBS["research-integrity.yml"],
         "main reviewed Research integrity source not exact")
    return {
        **results,"contexts":sorted(REQUIRED_JOBS),
        "required_context_names_unique":"exact full 30-file Git blob allowlist",
    }

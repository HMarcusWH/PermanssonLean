"""25+5 workflow profile mutation gates. No security approval is fabricated."""
import copy
import json
import unittest

import pr113_successor_workflow_profile as p

H="a"*40


def fixture():
    approved={f"original-{i:02}.yml":p.digest(
        f"name: original {i}\n".encode()) for i in range(25)}
    contents={".github/workflows/"+n:
              f"name: original {i}\n".encode()
              for i,n in enumerate(approved)}
    rows=[]
    proposed=sorted(p.PROPOSED)
    for name in proposed:
        staged=p.STAGED_PREFIX+name
        data=(
            "# REVIEW PENDING\n"
            f"name: PR113 {name}\n"
            "on:\n  push:\n    branches: [research/final-mathematical-closure]\n"
            "permissions:\n  contents: read\n"
            "jobs:\n"
            "  fixture:\n"
            "    steps:\n"
            "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262\n"
        )
        if name=="pr113-source-controls-v3_1.yml":
            data+=(
                "  original-legacy20:\n"
                "    name: legacy\n"
                "  original-legacy20-replay:\n"
                "    if: github.event_name == 'workflow_dispatch'\n"
                "    run: pr113_legacy20_choice_delivery.py\n"
                "    review_comment_id:\n"
            )
        raw=data.encode()
        contents[staged]=raw
        rows.append({
            "workflow_path":".github/workflows/"+name,
            "staged_source_path":staged,
            "git_blob_oid":p.git_blob_oid(raw),
            "source_unchanged":False,"approved":False,"installed":False,
        })
    manifest={
        "format":"Permansson.PR113.UnreviewedWorkflowProposals.v1",
        "status":"SOURCE_STAGED_NONEXECUTABLE_PENDING_INDEPENDENT_SECURITY_REVIEW",
        "original_approved_workflow_count":25,
        "historic_T":p.T,"base_B":p.B113,
        "independent_security_review":False,
        "owner_authorized_activation":False,
        "mathematical_acceptance":False,
        "release_authorized":False,
        "proposals":rows,
    }
    contents[p.MANIFEST]=json.dumps(manifest).encode()
    listing=("\n".join(sorted(".github/workflows/"+n
                              for n in approved))+"\n").encode()
    return approved,contents,listing


class WorkflowProfileTests(unittest.TestCase):
    def test_explicit_25_plus_5_not_activation(self):
        approved,files,tree=fixture()
        report=p.audit(H,read=files.__getitem__,
                       tree=lambda:tree,approved=approved)
        self.assertEqual(report["original_workflow_count"],25)
        self.assertEqual(report["proposed_future_workflow_count"],30)
        self.assertFalse(report["independent_security_review"])
        self.assertFalse(report["owner_activation_authorized"])
        self.assertFalse(report["publication_authorized"])

    def test_new_active_file_not_granted_historical_status(self):
        approved,files,tree=fixture()
        tree+=b".github/workflows/unreviewed.yml\n"
        with self.assertRaises(p.ProfileError):
            p.audit(H,read=files.__getitem__,tree=lambda:tree,approved=approved)

    def test_original_workflow_bytes_remain_immutable(self):
        approved,files,tree=fixture()
        files[".github/workflows/original-00.yml"]=b"permissions: write\n"
        with self.assertRaises(p.ProfileError):
            p.audit(H,read=files.__getitem__,tree=lambda:tree,approved=approved)

    def test_modified_staged_bytes_and_unpinned_action_rejected(self):
        approved,files,tree=fixture()
        target=p.STAGED_PREFIX+"pr113-preseal-fullscope.yml"
        files[target]+=b"  checks: write\n"
        with self.assertRaises(p.ProfileError):
            p.audit(H,read=files.__getitem__,tree=lambda:tree,approved=approved)
        approved,files,tree=fixture()
        row=json.loads(files[p.MANIFEST])
        files[target]+=b"  checks: write\n"
        rec=next(x for x in row["proposals"] if
                 x["staged_source_path"]==target)
        rec["git_blob_oid"]=p.git_blob_oid(files[target])
        files[p.MANIFEST]=json.dumps(row).encode()
        with self.assertRaises(p.ProfileError):
            p.audit(H,read=files.__getitem__,tree=lambda:tree,approved=approved)

    def test_fake_owner_authorization_in_staged_manifest_rejected(self):
        approved,files,tree=fixture()
        record=json.loads(files[p.MANIFEST])
        record["owner_authorized_activation"]=True
        files[p.MANIFEST]=json.dumps(record).encode()
        with self.assertRaises(p.ProfileError):
            p.audit(H,read=files.__getitem__,tree=lambda:tree,approved=approved)


if __name__=="__main__":
    unittest.main()

"""Adversarial tests for an inactive, byte-pinned original producer trigger plan."""
import copy
import unittest

import pr113_original_producer_trigger_candidate as trg

H="a"*40


def original(name, job, count):
    return (
        "name: PR113 "+name+"\n\n"+
        "on:\n"+
        "  push:\n"+
        "    branches: [research/final-mathematical-closure]\n"+
        "    paths:\n"+
        "      - 'verification/research/final_closure_*'\n"+
        "  workflow_dispatch:\n\n"+
        "permissions:\n  contents: read\n\n"+
        "jobs:\n  "+job+":\n"+
        "    strategy:\n      matrix:\n"+
        "        shard: ["+", ".join(str(i) for i in range(count))+"]\n"+
        "    steps:\n"+
        "      - run: python producer.py --shard-count "+str(count)+"\n"
    ).encode()


def fixture():
    specs=[
        ("pr113-all-case-compiler.yml","All-Case Compiler Candidate",
         "compiler-shard",4),
        ("pr113-all-original-semantic-candidates.yml","All Original Semantic Candidate Evidence",
         "semantic-candidate-shard",9),
        ("pr113-legacy-semantic-evidence.yml","Legacy Original Semantic Compiler Candidates",
         "legacy-original-shard",8),
    ]
    bytes_={}
    records=[]
    for name,label,job,n in specs:
        old=".github/workflows/"+name
        new="docs/operations/pr113_unapproved_workflows/trigger_candidates/"+name
        source=original(label,job,n)
        revised=trg.revised(source)
        bytes_[old]=source;bytes_[new]=revised
        records.append({
            "active":old,"proposal":new,
            "original_blob":trg.blob_oid(source),
            "proposed_blob":trg.blob_oid(revised),
            "producer_shards":n,"expected_job":job,
        })
    manifest={
        "format":"Permansson.PR113.StagedFullProducerTriggerReview.v1",
        "status":"REVIEW_PENDING__ACTIVE_WORKFLOWS_UNCHANGED",
        "original_requested_producer_jobs":21,
        "independent_security_review":False,
        "owner_approved_installation":False,
        "mathematical_acceptance":False,
        "publication_authorized":False,
        "proposals":records,
    }
    return manifest,bytes_


class FullProducerTriggerTests(unittest.TestCase):
    def validate(self,manifest,bytes_):
        return trg.validate_proposals(H,manifest,lambda h,path: bytes_[path])

    def test_all_4_9_8_source_jobs_retained_without_approval(self):
        m,b=fixture()
        outcome=self.validate(m,b)
        self.assertEqual(outcome["original_shard_count"],21)
        self.assertEqual(outcome["original_producing_workflow_count"],3)
        self.assertFalse(outcome["installed"])
        self.assertFalse(outcome["independent_security_review"])
        self.assertFalse(outcome["publication_authorized"])

    def test_changed_body_rejected_even_with_new_blob_hash(self):
        m,b=fixture()
        row=m["proposals"][0]
        b[row["proposal"]]=b[row["proposal"]].replace(
            b"--shard-count 4",b"--shard-count 3")
        row["proposed_blob"]=trg.blob_oid(b[row["proposal"]])
        with self.assertRaises(trg.TriggerReviewError):
            self.validate(m,b)

    def test_missing_original_source_or_staged_file_rejected(self):
        m,b=fixture()
        del b[m["proposals"][1]["active"]]
        with self.assertRaises(KeyError):
            self.validate(m,b)
        m,b=fixture()
        del b[m["proposals"][1]["proposal"]]
        with self.assertRaises(KeyError):
            self.validate(m,b)

    def test_old_or_candidate_oid_substitution_rejected(self):
        for key in ("original_blob","proposed_blob"):
            m,b=fixture()
            m["proposals"][0][key]="b"*40
            with self.subTest(key=key), self.assertRaises(trg.TriggerReviewError):
                self.validate(m,b)

    def test_no_source_beyond_trigger_may_be_changed(self):
        m,b=fixture()
        path=m["proposals"][2]["proposal"]
        b[path]=b[path].replace(b"permissions:\n  contents: read",
                                b"permissions:\n  contents: write")
        m["proposals"][2]["proposed_blob"]=trg.blob_oid(b[path])
        with self.assertRaises(trg.TriggerReviewError):
            self.validate(m,b)

    def test_review_status_cannot_be_self_promoted(self):
        for key in ("independent_security_review","owner_approved_installation",
                    "mathematical_acceptance","publication_authorized"):
            m,b=fixture()
            m[key]=True
            with self.subTest(key=key),self.assertRaises(trg.TriggerReviewError):
                self.validate(m,b)

    def test_missing_duplicate_or_foreign_job_rejected(self):
        m,b=fixture()
        m["proposals"].pop()
        with self.assertRaises(trg.TriggerReviewError):
            self.validate(m,b)
        m,b=fixture()
        m["proposals"][1]=copy.deepcopy(m["proposals"][0])
        with self.assertRaises(trg.TriggerReviewError):
            self.validate(m,b)
        m,b=fixture()
        m["proposals"][0]["expected_job"]="unreviewed-shortcut"
        with self.assertRaises(trg.TriggerReviewError):
            self.validate(m,b)

    def test_original_nondefault_branch_filter_cannot_be_kept(self):
        m,b=fixture()
        first=m["proposals"][0]
        b[first["proposal"]]=b[first["active"]]
        first["proposed_blob"]=trg.blob_oid(b[first["proposal"]])
        with self.assertRaises(trg.TriggerReviewError):
            self.validate(m,b)

    def test_unexpected_legacy_matrix_count_cannot_be_substituted(self):
        m,b=fixture()
        m["proposals"][2]["producer_shards"]=7
        with self.assertRaises(trg.TriggerReviewError):
            self.validate(m,b)


if __name__=="__main__":
    unittest.main()

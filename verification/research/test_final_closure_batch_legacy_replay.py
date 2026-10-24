"""Twenty-case original-provider selection tests, not mathematical approvals."""
import copy
import unittest
import final_closure_batch_legacy_replay as replay

IDS={f"L-{i:02d}" for i in range(20)}

def fixture():
    return {
        "format":"Permansson.PR113.LegacyReplaySelection.v1",
        "cases":[{
            "case_id":cid,"test_index":0,
            "test_method":"test_false_lean",
            "original_provider":"PermanssonResearch/Probability/Original.lean",
            "observation_id":"obs_"+cid.replace("-","_"),
            "producing_artifact_id":100+i,
        } for i,cid in enumerate(sorted(IDS))]
    }

class OriginalLegacySelectionTests(unittest.TestCase):
    def test_all_twenty_typed_choices_are_required(self):
        rows=replay.parse_mapping(fixture(),IDS)
        self.assertEqual(set(rows),IDS)
        self.assertEqual(len(rows),20)

    def test_missing_duplicate_foreign_and_unreviewed_fields_rejected(self):
        mutants=[]
        x=fixture();x["cases"].pop();mutants.append(x)
        x=fixture();x["cases"][1]["case_id"]=x["cases"][0]["case_id"];mutants.append(x)
        x=fixture();x["cases"][1]["case_id"]="UNLISTED";mutants.append(x)
        x=fixture();x["cases"][1]["test_method"]="other";mutants.append(x)
        x=fixture();x["cases"][1]["test_index"]=True;mutants.append(x)
        x=fixture();x["cases"][1]["producing_artifact_id"]=None;mutants.append(x)
        x=fixture();x["cases"][1]["original_provider"]="../escape.lean";mutants.append(x)
        x=fixture();x["cases"][1]["unauthorized_review"]="APPROVED";mutants.append(x)
        for idx,item in enumerate(mutants):
            with self.subTest(idx=idx),self.assertRaises(replay.LegacyBatchError):
                replay.parse_mapping(item,IDS)

    def test_selection_scope_cannot_be_shrunk_to_eight_shards(self):
        with self.assertRaises(replay.LegacyBatchError):
            replay.parse_mapping(fixture(),set(sorted(IDS)[:8]))

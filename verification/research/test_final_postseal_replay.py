"""Postseal candidate negative tests; never claim real authentication."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock
import zipfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "release/mathematical-closure-1"))
import postseal_replay as replay
from seal_approved import SealError

class PostsealTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        self.folder = root / "candidate"
        self.folder.mkdir()
        self.archive = self.folder / "Permansson_Mathematical_Closure_CANDIDATE.zip"
        self.sidecar = self.folder / "SHA256SUMS.txt"
        self.out = root / "detached" / "replay.json"
        self.manifest = {
            "format": "Permansson.MathClosure.CandidateSeal.v1",
            "status": "CANDIDATE_SEAL_BUILT", "full45_claimed": True,
            "accepted_case_count": 45, "accepted_claim_count": 11,
            "source_commit_sha": "a"*40, "head_sha": "b"*40,
            "pdf_sha256": "c"*64,
        }
        self.make_zip()

    def make_zip(self):
        with zipfile.ZipFile(self.archive, "w") as z:
            z.writestr("approved_seal.json", json.dumps(self.manifest))
        with zipfile.ZipFile(self.archive) as z:
            mb = z.read("approved_seal.json")
        self.sidecar.write_text(
            replay.sha(self.archive.read_bytes())+"  "+self.archive.name+"\n"+
            replay.sha(mb)+"  approved_seal.json\n")

    def test_replay_always_stays_unapproved(self):
        with mock.patch.object(replay, "verify_approved_archive", return_value=True):
            result = replay.replay(self.archive, self.sidecar, self.out)
        self.assertFalse(result["authenticated_ci_artifact"])
        self.assertFalse(result["full_release_approved"])
        self.assertEqual(result["status"], "CANDIDATE_ARCHIVE_REPLAYED_UNREVIEWED")

    def test_original_input_symlinks_and_ancestor_links_fail_closed(self):
        other = self.folder / "alias.zip"
        other.symlink_to(self.archive)
        with mock.patch.object(replay, "verify_approved_archive", return_value=True):
            with self.assertRaises(SealError):
                replay.replay(other, self.sidecar, self.out)
        other.unlink()
        sidecar_alias = self.folder / "alias.sha256"
        sidecar_alias.symlink_to(self.sidecar)
        with mock.patch.object(replay, "verify_approved_archive", return_value=True):
            with self.assertRaises(SealError):
                replay.replay(self.archive, sidecar_alias, self.out)
        sidecar_alias.unlink()
        parent_alias = self.folder.parent / "alias-dir"
        parent_alias.symlink_to(self.folder, target_is_directory=True)
        with mock.patch.object(replay, "verify_approved_archive", return_value=True):
            with self.assertRaises(SealError):
                replay.replay(parent_alias / self.archive.name,
                              self.sidecar, self.out)
            with self.assertRaises(SealError):
                replay.replay(self.archive, self.sidecar,
                              parent_alias / "replay.json")
        self.assertFalse(self.out.exists())

    def test_wrong_sidecar_fails(self):
        self.sidecar.write_text("bad checksum\n")
        with mock.patch.object(replay, "verify_approved_archive", return_value=True):
            with self.assertRaises(SealError):
                replay.replay(self.archive, self.sidecar, self.out)
        self.assertFalse(self.out.exists())

    def test_incomplete_claims_and_existing_output_fail(self):
        self.manifest["accepted_claim_count"] = 10
        self.make_zip()
        with mock.patch.object(replay, "verify_approved_archive", return_value=True):
            with self.assertRaises(SealError):
                replay.replay(self.archive, self.sidecar, self.out)
        self.manifest["accepted_claim_count"] = 11
        self.make_zip()
        self.out.parent.mkdir(parents=True)
        self.out.write_text("KEEP")
        with mock.patch.object(replay, "verify_approved_archive", return_value=True):
            with self.assertRaises(SealError):
                replay.replay(self.archive, self.sidecar, self.out)
        self.assertEqual(self.out.read_text(), "KEEP")

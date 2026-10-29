"""R05/R07: real source-control validation across a synthetic GH input carrier.

The producer ZIPs and reviewer/GitHub responses are synthetic. This
rehearsal authenticates *no real CI, mathematical review or publication*.
"""
from __future__ import annotations

import io
import json
from pathlib import Path
import tempfile
import unittest
import zipfile

from pr113_preseal_input_carrier import (
    EXPECTED_FILES, PresealInputError, digest, extract,
)
from pr113_v31_execution_integrity import (
    RealControlError, validate_executed_controls,
)
from test_pr113_preseal_input_carrier import originals
from test_pr113_v31_execution_integrity import (
    H, authentic_original_legacy, complete, source,
)


def encoded(value):
    return (json.dumps(value, sort_keys=True) + "\n").encode("utf-8")


def zipped(members):
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w", zipfile.ZIP_DEFLATED) as handle:
        for name, raw in sorted(members.items()):
            handle.writestr(name, raw)
    return buffer.getvalue()


def synthetic_carrier(contract, archives):
    """Keep all three genuine-shaped 45+20+11 owner archives byte-exact."""
    members = {
        "reviewed/approved_claim_manifest.json": encoded({
            "status": "SYNTHETIC_UNREVIEWED", "claims": [],
        }),
        "reviewed/source_receipts.json": encoded({
            "format": "SYNTHETIC_NOT_A_GITHUB_RECEIPT",
            "head_sha": H, "independent_review": False,
        }),
        "reviewed/evidence_bundle.zip": zipped({
            "mock.txt": b"unreviewed source evidence placeholder",
        }),
        "reviewed/reproduction.zip": zipped({
            "mock.txt": b"unreviewed reproduction placeholder",
        }),
        "reviewed/reproduction_ids.json": encoded({
            "status": "SYNTHETIC_NOT_REPRODUCTION",
        }),
        "reviewed/additional_contract.json": encoded(contract),
        "reviewed/workflow_blob_candidates.json": encoded({
            "status": "SYNTHETIC_UNREVIEWED",
        }),
    }
    # This synthetic connected fixture represents a full 76-owner registry
    # over only three producer ZIPs; the real validator still authenticates
    # every run/check/artifact byte in subsequent separate stages.
    contract = {
        **contract,
        "format": "Permansson.PR113.ControlProducerExtension.v3.1",
        "source_controls_accepted": False,
        "independent_security_review": False,
        "mathematical_approval": False,
    }
    members["reviewed/additional_contract.json"] = encoded(contract)
    for artifact_id, raw in archives.items():
        members[f"reviewed/additional_zips/{artifact_id}.zip"] = raw
    assert EXPECTED_FILES <= set(members)
    return zipped(members)


class ConnectedSourceCarrierTests(unittest.TestCase):
    def test_76_owner_source_validation_survives_carrier_exactly(self):
        contract, owner_archives = complete()
        original_21 = authentic_original_legacy()
        first = validate_executed_controls(
            H, contract, owner_archives,
            source=source(), original_producers=original_21)
        self.assertEqual(first["source_owner_count"], 76)
        self.assertEqual(first["claim_positive_negative_directions"], 22)
        self.assertFalse(first["mathematical_acceptance"])
        raw = synthetic_carrier(contract, owner_archives)

        with tempfile.TemporaryDirectory(prefix="pr113-r05-r07-") as td:
            base = Path(td)
            artifact = base / "original-carrier.zip"
            artifact.write_bytes(raw)
            gh = originals(raw)
            gh.pop("raw")
            output = base / "unpacked"
            transport = extract(artifact, output, **gh)

            self.assertEqual(
                transport["status"],
                "GH_SOURCE_TRANSPORT_VERIFIED__RELEASE_REVIEW_PENDING")
            self.assertEqual(transport["transport_artifact_sha256"], digest(raw))
            self.assertFalse(transport["independent_review"])
            self.assertFalse(transport["mathematical_acceptance"])
            self.assertFalse(transport["publication_authorized"])
            self.assertEqual(
                json.loads((output / "transport_diagnostics.json").read_bytes()),
                transport)

            recovered_contract = json.loads(
                (output / "additional_contract.json").read_bytes())
            recovered_archives = {
                number: (output / "additional_zips" /
                         f"{number}.zip").read_bytes()
                for number in owner_archives
            }
            self.assertEqual(recovered_archives, owner_archives)
            second = validate_executed_controls(
                H, recovered_contract, recovered_archives,
                source=source(), original_producers=original_21)
            self.assertEqual(first, second)
            self.assertFalse(json.loads(
                (output / "source_receipts.json").read_bytes()
            )["independent_review"])

            # A different valid ZIP at the claimed artifact ID must not
            # inherit another owner's original execution provenance.
            recovered_archives[1], recovered_archives[2] = (
                recovered_archives[2], recovered_archives[1])
            with self.assertRaises(RealControlError):
                validate_executed_controls(
                    H, recovered_contract, recovered_archives,
                    source=source(), original_producers=original_21)

    def test_missing_original_producers_and_foreign_head_fail(self):
        contract, archives = complete()
        with self.assertRaises(RealControlError):
            validate_executed_controls(
                H, contract, archives, source=source(),
                original_producers=None)
        foreign = dict(contract, head_sha="b" * 40)
        with self.assertRaises(RealControlError):
            validate_executed_controls(
                H, foreign, archives, source=source(),
                original_producers=authentic_original_legacy())

    def test_forged_github_artifact_digest_fails_before_unpack(self):
        contract, archives = complete()
        raw = synthetic_carrier(contract, archives)
        with tempfile.TemporaryDirectory(prefix="pr113-bad-gh-") as td:
            base = Path(td)
            archive = base / "original.zip"
            archive.write_bytes(raw)
            gh = originals(raw)
            gh.pop("raw")
            gh["meta"]["digest"] = "sha256:" + ("0" * 64)
            output = base / "rejected"
            with self.assertRaises(PresealInputError):
                extract(archive, output, **gh)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()

"""Reviewed production identities and limits. No environment or CLI overrides."""

from dataclasses import dataclass

FROZEN_CORE = "c018f79ea4ce46f4f679ad5bca254509778fc53c"
HISTORICAL_BASELINE = "6191a1acbf00867042a21c8e6c4a532af43017bc"
RESEARCH_SOURCE = "5822cdff0fc360d9e368e10ff5f7576c3141a1b3"
ACCEPTED_RELEASE = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"
ACCEPTED_RELEASE_TREE = "72ad841cc5b3cffc5f82979a9739b7fd03d75e15"
RELEASE_PR_HEAD = "cdbe7ed5124781be495404122fac1de3315cb6ec"
RELEASE_PR_SYNTHETIC = "c70362b97ae7d0828a569fa15e194f9861b22b46"

SHA256_PINS = {
    "manifest": "6065ec5431430f6804ebabffe636170d8bb349f08cfa817776b05a85bb6fe127",
    "manuscript": "8022291f1ec19961578bdcb60f205fdec31057982bf9a78f6b9610bd3b184239",
    "builder": "a711fce840920846e9ffdd55b2580ebe358233ca7b432bffa78af315be69ffa6",
    "verifier": "abe1cd70491b4976ab7e3d1f06c405508e2fde7e3890f818a89b97ed88841dc2",
    "tex": "3524da1f1ef92cfee179917efebeb3c2786b8ad484653d2f1c8f4d8036952416",
    "release_zip": "4db31db5b805ad2f455f27e5a2e013cd13ea257984e174f6453af8f8db5b1f6c",
}

MANIFEST_PATH = b"release/v0.2.0/manifest.json"
TEX_PATH = b"release/v0.2.0/output/pdf/Permansson_Research_Companion_v0.2.0.tex"
RELEASE_OUTER_PATHS = (
    b"release/Permansson_v0.2.0_research-kit.zip",
    b"release/Permansson_v0.2.0_research-kit.zip.sha256",
)
CLOSED_ROOTS = (
    b"PermanssonLean", b"paper", b"provenance", b"application",
    b"verification/destructive", b"verification/v0.1.8_release_gate",
    b"verification/lean", b"release/v0.2.0",
)
SENSITIVE_ROOTS = (
    b"verification/integrity", b"verification/archive", b".github/workflows",
    b".github/repository-rules",
)
MANIFEST_LIMIT = 2 * 1024 * 1024
PROTECTED_BLOB_LIMIT = 64 * 1024 * 1024
PROTECTED_TOTAL_LIMIT = 128 * 1024 * 1024
GIT_TIMEOUT = 60
TEX_TIMEOUT = 30
TEX_OUTPUT_LIMIT = 2 * 1024 * 1024
TEX_EXPECTED_SIZE = 71379
BUNDLE_LIMIT = 256 * 1024 * 1024
OBJECT_TOTAL_LIMIT = 1024 * 1024 * 1024
OBJECT_COUNT_LIMIT = 200000
OBJECT_LIMIT = 128 * 1024 * 1024
METADATA_LIMIT = 8 * 1024 * 1024
DIFFERENCE_LIMIT = 1000


@dataclass(frozen=True)
class _InventoryPolicy:
    """Internal fixture seam; production commands always use PRODUCTION_POLICY."""

    accepted_release: str
    accepted_tree: str
    historical_baseline: str
    research_source: str
    manifest_sha256: str
    historical_count: int = 340
    release_count: int = 29
    manifest_path: bytes = MANIFEST_PATH
    release_root: bytes = b"release/v0.2.0"
    outer_paths: tuple[bytes, ...] = RELEASE_OUTER_PATHS
    closed_roots: tuple[bytes, ...] = CLOSED_ROOTS


PRODUCTION_POLICY = _InventoryPolicy(
    ACCEPTED_RELEASE, ACCEPTED_RELEASE_TREE, HISTORICAL_BASELINE,
    RESEARCH_SOURCE, SHA256_PINS["manifest"],
)

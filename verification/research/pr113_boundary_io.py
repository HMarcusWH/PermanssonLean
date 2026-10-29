"""Strict, nonauthorizing intake helpers for post-PR113 evidence consumers.

These helpers validate local bytes and paths. They NEVER authenticate GitHub
identities or independently authorize review, merge, claims or publication.
"""
from __future__ import annotations

import json
from pathlib import Path
import urllib.parse
import urllib.request

MAX_REDIRECTS = 5


class BoundaryError(ValueError):
    pass


def strict_json_object(raw: bytes, *, max_bytes: int = 4 * 1024 * 1024) -> dict:
    if (type(raw) is not bytes or type(max_bytes) is not int
            or not 0 < max_bytes <= 8 * 1024 * 1024
            or not 0 < len(raw) <= max_bytes):
        raise BoundaryError("JSON source missing or unbounded")

    def unique(pairs):
        out = {}
        for key, value in pairs:
            if key in out:
                raise BoundaryError("duplicate JSON key: " + key)
            out[key] = value
        return out

    def invalid_constant(value):
        raise BoundaryError("nonfinite JSON number: " + value)

    try:
        result = json.loads(raw, object_pairs_hook=unique,
                            parse_constant=invalid_constant)
    except BoundaryError:
        raise
    except (UnicodeError, ValueError, TypeError) as exc:
        raise BoundaryError("JSON source malformed") from exc
    if type(result) is not dict:
        raise BoundaryError("JSON source must be an object")
    return result


def detached_destination(path, source_root, *, forbidden=(), must_exist=False):
    """Resolve a safe, unsymlinked, fresh external path before writing.

    Existing output paths are rejected unless explicitly opened for read.
    Opaque symlinks and parent traversal are rejected *before* canonicalization.
    """
    candidate = Path(path).expanduser()
    if ".." in candidate.parts:
        raise BoundaryError("parent-traversing detached evidence path")
    absolute = candidate.absolute()
    if any(part.is_symlink() for part in (absolute, *absolute.parents)):
        raise BoundaryError("symlinked detached evidence path")
    resolved = absolute.resolve(strict=False)
    if resolved.exists() != bool(must_exist):
        raise BoundaryError("detached evidence path existence mismatch")
    if must_exist and not resolved.is_file():
        raise BoundaryError("detached evidence must be a regular file")
    roots = (source_root, *forbidden)
    for root in roots:
        original = Path(root).resolve()
        if resolved == original or resolved.is_relative_to(original):
            raise BoundaryError("detached evidence path resides within protected root")
    return resolved


def approved_artifact_url(value):
    try:
        part = urllib.parse.urlsplit(value)
        host = (part.hostname or "").lower().rstrip(".")
        return (part.scheme == "https" and part.port in (None, 443)
                and part.username is None and part.password is None
                and not part.fragment
                and (host == "api.github.com"
                     or host.endswith(".githubusercontent.com")
                     or host.endswith(".blob.core.windows.net")
                     or host.endswith(".amazonaws.com")))
    except (TypeError, ValueError):
        return False


class BoundedArtifactRedirect(urllib.request.HTTPRedirectHandler):
    def __init__(self):
        super().__init__()
        self.hops = 0

    def redirect_request(self, req, fp, code, msg, headers, newurl):
        self.hops += 1
        if self.hops > MAX_REDIRECTS or not approved_artifact_url(newurl):
            raise BoundaryError("artifact redirect escaped approved HTTPS hosts")
        child = super().redirect_request(req, fp, code, msg, headers, newurl)
        if child is None:
            raise BoundaryError("artifact redirect rejected")
        # The bearer token may only accompany the initial literal GitHub API.
        # Never allow a redirected request to carry authorization, even if
        # redirect target or source is another API endpoint.
        for mapping in (child.headers, child.unredirected_hdrs):
            for key in list(mapping):
                if key.lower() == "authorization":
                    del mapping[key]
        return child


def github_artifact_zip(repository, artifact_id, token, *, max_bytes):
    if (type(artifact_id) is not int or artifact_id <= 0
            or type(max_bytes) is not int or not 0 < max_bytes <= 256*1024*1024
            or not isinstance(token, str) or not token):
        raise BoundaryError("artifact request lacks bounded original source")
    if repository != "HMarcusWH/PermanssonLean":
        raise BoundaryError("foreign artifact repository")
    url = ("https://api.github.com/repos/" + repository
           + "/actions/artifacts/" + str(artifact_id) + "/zip")
    if not approved_artifact_url(url):
        raise BoundaryError("untrusted artifact API origin")
    request = urllib.request.Request(url, headers={
        "User-Agent": "Permansson-ReadOnlyOriginalArtifact/2",
        "Accept": "application/vnd.github+json",
        "Authorization": "Bearer " + token,
    })
    opener = urllib.request.build_opener(BoundedArtifactRedirect())
    with opener.open(request, timeout=55) as response:
        size = response.headers.get("Content-Length")
        if size is not None and int(size) > max_bytes:
            raise BoundaryError("original ZIP exceeds compressed-byte budget")
        data = response.read(max_bytes + 1)
    if not 0 < len(data) <= max_bytes or not data.startswith(b"PK"):
        raise BoundaryError("original ZIP unavailable, truncated, or oversized")
    return data

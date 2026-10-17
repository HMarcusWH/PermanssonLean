"""Fail-closed Linux network-namespace adapter for historical artifact replay."""
from __future__ import annotations

import argparse
from dataclasses import replace
import errno
import importlib.metadata
import os
from pathlib import Path
import platform
import socket
import subprocess
import sys
import tempfile

from verification.integrity.git_objects import GitRepo
from verification.integrity.reports import HardeningError, check_report, write_report
from .manifest import MAX_METADATA, fail, read_bounded, strict_json


def invocation_context(repo_path=None, candidate=None):
    """CI always binds C; standalone local replay may acquire A after restore."""
    from verification.integrity.ci_context import capture_context
    try:
        repo = GitRepo(repo_path or ".")
    except HardeningError as exc:
        if (repo_path is None and candidate is None and os.environ.get("GITHUB_ACTIONS") != "true"
                and exc.code == "E_REFERENCE_MISSING"):
            return None
        raise
    target = candidate or repo.run("rev-parse", "HEAD").decode().strip()
    return capture_context(repo, target)


def restored_artifact_context(scratch):
    from verification.integrity.ci_context import capture_context
    from .create_bundle import ACCEPTED
    if os.environ.get("GITHUB_ACTIONS") == "true":
        fail("E_CONTEXT", "A historical replay cannot substitute for genuine candidate CI")
    repo = GitRepo(Path(scratch) / "accepted")
    context = capture_context(repo, ACCEPTED)
    return replace(context, scope="accepted_artifact_replay")


def isolation_attestation(parent_namespace):
    if platform.system() != "Linux" or not parent_namespace:
        fail("E_NETWORK_NOT_ISOLATED", "A Linux parent network-namespace identity is required", 3)
    try:
        namespace = os.readlink("/proc/self/ns/net")
        status = dict(line.split(":", 1) for line in Path("/proc/self/status").read_text().splitlines() if ":" in line)
        routes = Path("/proc/net/route").read_text().splitlines()[1:]
        ipv6 = Path("/proc/net/ipv6_route").read_text().splitlines()
    except OSError as exc:
        raise HardeningError("E_NETWORK_NOT_ISOLATED", "Cannot attest Linux isolation", 3) from exc
    if namespace == parent_namespace:
        fail("E_NETWORK_NOT_ISOLATED", "Child still uses the parent's network namespace")
    if os.getuid() == 0 or os.getgid() == 0 or os.getgroups():
        fail("E_NETWORK_NOT_ISOLATED", "Archive parser must run nonroot with no supplementary groups")
    if any(int(status.get(name, "1").strip(), 16) != 0 for name in ("CapInh", "CapPrm", "CapEff", "CapBnd", "CapAmb")):
        fail("E_NETWORK_NOT_ISOLATED", "Archive parser retained Linux capabilities")
    if status.get("NoNewPrivs", "").strip() != "1":
        fail("E_NETWORK_NOT_ISOLATED", "No-new-privileges is not active")
    if any(line.split()[0] != "lo" for line in routes if line.split()):
        fail("E_NETWORK_NOT_ISOLATED", "An outward IPv4 route remains")
    if any(line.split()[-1] != "lo" for line in ipv6 if line.split()):
        fail("E_NETWORK_NOT_ISOLATED", "An outward IPv6 route remains")
    denied = None
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as outbound:
        outbound.settimeout(2)
        try:
            outbound.connect(("203.0.113.1", 9))
        except OSError as exc:
            if exc.errno in {errno.ENETUNREACH, errno.EHOSTUNREACH, errno.EPERM, errno.EACCES}:
                denied = exc.errno
            else:
                fail("E_NETWORK_NOT_ISOLATED", "Outward socket failed without a conclusive isolation denial")
        else:
            fail("E_NETWORK_NOT_ISOLATED", "Outward socket unexpectedly connected")
    return {"parent_network_namespace": parent_namespace, "child_network_namespace": namespace,
            "uid": os.getuid(), "gid": os.getgid(), "supplementary_groups": [],
            "capabilities": "all_zero", "no_new_privileges": True,
            "outward_routes": [], "outward_socket_denied_errno": denied,
            "network_isolation": "ENFORCED"}


def require_dependencies():
    try:
        version = importlib.metadata.version("pypdf")
    except importlib.metadata.PackageNotFoundError:
        fail("E_DEPENDENCY_MISSING", "Install pypdf==6.10.0 before entering offline replay", 3)
    if version != "6.10.0":
        fail("E_DEPENDENCY_MISSING", "Offline replay requires pypdf==6.10.0", 3)
    if sys.version_info[:2] != (3, 13):
        fail("E_DEPENDENCY_MISSING", "The supported offline replay profile requires Python 3.13", 3)


def sanitized_environment():
    denied = ("TOKEN", "PASSWORD", "COOKIE", "SECRET", "AUTHORIZATION", "CREDENTIAL", "PROXY")
    environment = {key: value for key, value in os.environ.items()
                   if not any(word in key.upper() for word in denied)
                   and not key.startswith(("GIT_", "GH_", "GITHUB_", "AWS_", "AZURE_", "GOOGLE_"))
                   and key not in {"PYTHONPATH", "PYTHONHOME", "PERMANSSON_PARENT_NETNS"}}
    environment.update({"PYTHONDONTWRITEBYTECODE": "1", "LC_ALL": "C", "CI": ""})
    return environment


def launch_offline(supplement, scratch):
    """No archive parser runs through sudo: privileges drop before Python starts."""
    if platform.system() != "Linux" or os.getuid() == 0 or os.getgid() == 0:
        fail("E_OFFLINE_UNAVAILABLE", "Supported isolation requires a nonroot Linux runner", 3)
    require_dependencies()
    programs = [Path(name) for name in ("/usr/bin/sudo", "/usr/bin/unshare", "/usr/bin/setpriv")]
    if any(not path.is_file() or not os.access(path, os.X_OK) for path in programs):
        fail("E_OFFLINE_UNAVAILABLE", "Required namespace/privilege executables are unavailable", 3)
    parent = os.readlink("/proc/self/ns/net")
    worker = Path(__file__).with_name("_offline_worker.py").resolve()
    with tempfile.TemporaryDirectory(prefix="permansson-offline-report-") as temporary:
        output = Path(temporary) / "worker.json"
        command = [str(programs[0]), "-n", str(programs[1]), "--net", "--", str(programs[2]),
                   "--reuid=" + str(os.getuid()), "--regid=" + str(os.getgid()), "--clear-groups",
                   "--bounding-set=-all", "--inh-caps=-all", "--ambient-caps=-all", "--no-new-privs",
                   sys.executable, "-B", str(worker), "--supplement", str(Path(supplement).absolute()),
                   "--scratch", str(Path(scratch).absolute()), "--report", str(output), "--parent-netns", parent]
        try:
            with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
                process = subprocess.Popen(command, env=sanitized_environment(), stdin=subprocess.DEVNULL,
                                           stdout=stdout, stderr=stderr, close_fds=True)
                try:
                    process.wait(timeout=1800)
                except subprocess.TimeoutExpired as exc:
                    process.kill()
                    process.wait()
                    raise HardeningError("E_COMMAND_TIMEOUT", "Offline replay exceeded 30 minutes") from exc
                stdout.seek(0)
                stderr.seek(0)
                diagnostic = (stdout.read(4096) + stderr.read(4096)).decode("utf-8", "replace")
        except OSError as exc:
            raise HardeningError("E_OFFLINE_UNAVAILABLE", "Namespace launch is unavailable", 3) from exc
        if not output.is_file():
            fail("E_OFFLINE_UNAVAILABLE", "No isolated worker attestation; no online fallback: " + diagnostic[-2000:], 3)
        result = strict_json(read_bounded(output))
        if result.get("status") != "PASS" or process.returncode:
            fail(result.get("error_code", "E_REPORT"), result.get("message", "Isolated worker failed"),
                 3 if result.get("status") == "BLOCKED" else 1)
        details = result.get("details", {})
        if (details.get("isolation", {}).get("network_isolation") != "ENFORCED"
                or details.get("isolation", {}).get("parent_network_namespace") != parent
                or details.get("isolation", {}).get("uid") != os.getuid()
                or details.get("isolation", {}).get("gid") != os.getgid()):
            fail("E_REPORT", "Isolated worker omitted or contradicted its isolation attestation")
        return details


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--supplement", required=True)
    parser.add_argument("--scratch", required=True)
    parser.add_argument("--report", required=True)
    parser.add_argument("--repo")
    parser.add_argument("--candidate")
    args = parser.parse_args(argv)
    context = None
    try:
        context = invocation_context(args.repo, args.candidate)
        details = launch_offline(args.supplement, args.scratch)
        if context is None:
            context = restored_artifact_context(args.scratch)
            details["acceptance_scope"] = "accepted_artifact_replay_only"
        payload = check_report("archive-reproducibility", context, details=details,
                               completed_stages=details["completed_stages"])
        code = 0
    except HardeningError as exc:
        payload = check_report("archive-reproducibility", context, "BLOCKED" if exc.exit_code == 3 else "FAIL", exc)
        code = exc.exit_code
    except Exception as exc:
        payload = check_report("archive-reproducibility", context, "FAIL", HardeningError("E_UNEXPECTED", str(exc)))
        code = 1
    write_report(args.report, payload)
    print("archive-reproducibility: " + payload["status"])
    return code


if __name__ == "__main__":
    raise SystemExit(main())

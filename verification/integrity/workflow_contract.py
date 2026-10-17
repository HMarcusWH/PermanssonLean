"""Review-sensitive structural contract for the three checked-in CI jobs."""
import re
from .reports import HardeningError

JOBS = {"frozen-source-preservation", "release-export-integrity", "archive-reproducibility"}
ACTION_PINS = {"actions/checkout": "11d5960a326750d5838078e36cf38b85af677262",
               "actions/setup-python": "a26af69be951a213d495a4c3e4e4022e16d87065",
               "actions/upload-artifact": "ea165f8d65b6e75b540449e92b4886f43607fa02"}


def validate_workflow(text):
    def reject(message):
        raise HardeningError("E_WORKFLOW_CONTRACT", message)
    if re.search(r"^\s*(paths|paths-ignore|needs|continue-on-error|secrets):", text, re.M):
        reject("Required checks cannot be filtered, skipped or fail open")
    for match in re.finditer(r"^\s*if:\s*(.*)$", text, re.M):
        if match.group(1).strip() != "always()" or not re.match(r"\s*uses: actions/upload-artifact@", text[match.end():]):
            reject("Only diagnostic artifact uploads may have a condition")
    if "pull_request_target" in text or "self-hosted" in text:
        reject("Privileged candidate execution is unsupported")
    if text.count("\npermissions:\n  contents: read\n") != 1:
        reject("Workflow token must be read-only")
    if "\n  pull_request:\n    branches: [main]\n" not in text or "\n  push:\n    branches: [main]\n" not in text:
        reject("Both main PR and main push events are required")
    if "\njobs:\n" not in text:
        reject("Missing jobs")
    jobs = text.split("\njobs:\n", 1)[1]
    if set(re.findall(r"^  ([a-z-]+):$", jobs, re.M)) != JOBS:
        reject("Job context names disagree with the deployment contract")
    for name, pin in re.findall(r"uses:\s*([^@\s]+)@([^\s]+)", text):
        if ACTION_PINS.get(name) != pin:
            reject("Unreviewed action or mutable action reference")
    if text.count("persist-credentials: false") != 3 or text.count("fetch-depth: 0") != 3:
        reject("Every job needs a full-history credential-free checkout")
    if text.count("-m verification.integrity.ci_context") != 3:
        reject("Every job must validate source context")
    required = ["verification.integrity.preservation", "verification.integrity.tex_export",
                "verification.archive.offline_smoke", "--suite reference", "--suite preservation",
                "--suite context", "--suite workflow", "--suite tex", "--suite archive"]
    if any(item not in text for item in required):
        reject("A required verifier or test suite is absent")
    blocks = re.split(r"^  ([a-z-]+):\n", jobs, flags=re.M)
    command_prefixes = {
        "frozen-source-preservation": ["python -B -m verification.integrity.ci_context ",
            "python -B -m verification.integrity.preservation ",
            *["python -B -m verification.integrity.run_tests --suite " + suite + " "
              for suite in ("reference", "preservation", "context", "workflow")]],
        "release-export-integrity": ["python -B -m verification.integrity.ci_context ",
            "python -B -m verification.integrity.tex_export ",
            "python -B -m verification.integrity.run_tests --suite tex "],
        "archive-reproducibility": ["python -B -m verification.integrity.ci_context ",
            "python -m pip install -r verification/integrity/requirements.txt",
            "python -B -m verification.integrity.run_tests --suite archive ",
            "python -B -m verification.archive.offline_smoke "],
    }
    for index in range(1, len(blocks), 2):
        name, body = blocks[index:index + 2]
        commands = []
        in_block = False
        for line in body.splitlines():
            if line.startswith("        run: "):
                value = line[len("        run: "):]
                in_block = value == "|"
                if not in_block:
                    commands.append(value)
            elif in_block and line.startswith("          ") and line.strip():
                commands.append(line.strip())
            elif line.strip():
                in_block = False
        expected = command_prefixes[name]
        if len(commands) != len(expected):
            reject("Job command count changed")
        for command, prefix in zip(commands, expected):
            if not command.startswith(prefix) or any(token in command for token in ("||", "&&", ";", "$(`", "$(", "`", " >", " |")):
                reject("Verification must execute directly and propagate its exit status")
    return {"contexts": sorted(JOBS), "publisher_binding": "requires live read-back"}

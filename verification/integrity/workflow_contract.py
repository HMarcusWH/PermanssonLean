"""Review-sensitive structural contract for the three checked-in CI jobs."""
import hashlib
import re
from .reports import HardeningError

JOBS = {"frozen-source-preservation", "release-export-integrity", "archive-reproducibility"}
ACTION_PINS = {"actions/checkout": "11d5960a326750d5838078e36cf38b85af677262",
               "actions/setup-python": "a26af69be951a213d495a4c3e4e4022e16d87065",
               "actions/upload-artifact": "ea165f8d65b6e75b540449e92b4886f43607fa02"}

# The structural checks below explain common failures; they are not a general
# YAML parser. Bind the entire reviewed canonical-LF profile as well, so ignored
# steps, event filters, action inputs or future YAML forms cannot silently alter
# effective execution. A profile change requires a separately reviewed update
# to this source constant. There is no runtime override. The candidate still
# owns this checker, so the pin does not authenticate its own human review.
APPROVED_WORKFLOW_SHA256 = "70cd7e8569beb995981be210369f57c34460289e6a5890c54153683a26939093"


def validate_workflow(text):
    def reject(message):
        raise HardeningError("E_WORKFLOW_CONTRACT", message)
    if re.search(r"^\s*(paths|paths-ignore|needs|continue-on-error|secrets):", text, re.M):
        reject("Required checks cannot be filtered, skipped or fail open")
    # This gate validates the deliberately narrow reviewed block-style profile,
    # not arbitrary YAML. Refuse forms that could hide effective mapping keys.
    if (re.search(r"(?:^|[ \t])![^\s]", text, re.M)
            or re.search(r"^[ \t]*%", text, re.M)
            or re.search(r"^[ \t]*(?:---|\.\.\.)(?:[ \t#]|$)", text, re.M)
            or re.search(r"^[ \t]*(?:-[ \t]*)?[&*][^\s]", text, re.M)):
        reject("YAML tags, directives, document markers and standalone anchors are unsupported")
    if (re.search(r"^[ \t]*(?:-[ \t]*)?[\"'].*?[\"'][ \t]*:", text, re.M)
            or re.search(r"^[ \t]*[?:][ \t]", text, re.M)
            or re.search(r":[ \t]*[&*{]", text)
            or re.search(r"^[ \t]*<<[ \t]*:", text, re.M)):
        reject("Quoted/explicit keys, aliases and flow mappings are outside the reviewed workflow profile")
    top_keys = re.findall(r"^([a-z][a-z-]*):", text, re.M)
    if len(top_keys) != 4 or set(top_keys) != {"name", "on", "permissions", "jobs"}:
        reject("Unexpected or duplicated top-level workflow configuration")
    if re.search(r"^[ \t]*(?:shell|defaults|env|environment|working-directory|container|services|strategy)[ \t]*:", text, re.M):
        reject("Execution, environment and job-shell overrides are outside the reviewed profile")
    if re.search(r"^[ \t]*workflow_dispatch[ \t]*:", text, re.M):
        reject("Required checks run only on genuine main PR and main push events")
    for match in re.finditer(r"^\s*if:\s*(.*)$", text, re.M):
        if match.group(1).strip() != "always()" or not re.match(r"\s*uses: actions/upload-artifact@", text[match.end():]):
            reject("Only diagnostic artifact uploads may have a condition")
    if "pull_request_target" in text or "self-hosted" in text:
        reject("Privileged candidate execution is unsupported")
    permission_keys = list(re.finditer(r"^([ \t]*)permissions[ \t]*:[^\r\n]*$", text, re.M))
    if (len(permission_keys) != 1 or permission_keys[0].group(1)
            or text.count("\npermissions:\n  contents: read\n") != 1):
        reject("Workflow token must be read-only")
    permission_body = []
    for line in text[permission_keys[0].end():].splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        if not line.startswith((" ", "\t")):
            break
        permission_body.append(line)
    if permission_body != ["  contents: read"]:
        reject("No token grants beyond the reviewed read-only contents permission are allowed")
    if re.search(r"\$\{\{\s*secrets[.\[]", text):
        reject("Required candidate jobs cannot receive repository secrets")
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
    if (re.findall(r"^[ \t]*persist-credentials:[ \t]*(.*)$", text, re.M) != ["false"] * 3
            or re.findall(r"^[ \t]*fetch-depth:[ \t]*(.*)$", text, re.M) != ["0"] * 3):
        reject("Every job needs a full-history credential-free checkout")
    if text.count("-m verification.integrity.ci_context") != 3:
        reject("Every job must validate source context")
    required = ["verification.integrity.preservation", "verification.integrity.tex_export",
                "verification.archive.offline_smoke", "--suite reference", "--suite preservation",
                "--suite context", "--suite workflow", "--suite tex", "--suite archive"]
    if any(item not in text for item in required):
        reject("A required verifier or test suite is absent")
    blocks = re.split(r"^  ([a-z-]+):\n", jobs, flags=re.M)
    context_command = 'python -B -m verification.integrity.ci_context --repo . --event-file "$GITHUB_EVENT_PATH" --report "$RUNNER_TEMP/context.json"'
    commands_by_job = {
        "frozen-source-preservation": [context_command,
            'python -B -m verification.integrity.preservation --repo . --candidate "$GITHUB_SHA" --report "$RUNNER_TEMP/preservation.json"',
            *["python -B -m verification.integrity.run_tests --suite " + suite + " "
              + '--report "$RUNNER_TEMP/' + suite + '-tests.json"'
              for suite in ("reference", "preservation", "context", "workflow")]],
        "release-export-integrity": [context_command,
            'python -B -m verification.integrity.tex_export --repo . --candidate "$GITHUB_SHA" --report "$RUNNER_TEMP/tex-export.json"',
            'python -B -m verification.integrity.run_tests --suite tex --report "$RUNNER_TEMP/tex-tests.json"'],
        "archive-reproducibility": [context_command,
            "python -m pip install -r verification/integrity/requirements.txt",
            'python -B -m verification.integrity.run_tests --suite archive --report "$RUNNER_TEMP/archive-tests.json"',
            'python -B -m verification.archive.offline_smoke --repo . --candidate "$GITHUB_SHA" --supplement archival/v0.2.0/supplement-1 --scratch "$RUNNER_TEMP/archive-clean" --report "$RUNNER_TEMP/archive-replay.json"'],
    }
    for index in range(1, len(blocks), 2):
        name, body = blocks[index:index + 2]
        job_keys = re.findall(r"^    ([a-z][a-z-]*):", body, re.M)
        if len(job_keys) != 3 or set(job_keys) != {"runs-on", "timeout-minutes", "steps"}:
            reject("Unexpected or duplicated effective job configuration")
        if "    runs-on: ubuntu-latest\n" not in body or "    timeout-minutes: 25\n" not in body:
            reject("Job runner and timeout differ from the reviewed execution profile")
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
        expected = commands_by_job[name]
        if len(commands) != len(expected):
            reject("Job command count changed")
        for command, approved in zip(commands, expected):
            if command != approved or any(token in command for token in ("&", "|", ";", "$(", "`", ">", "<")):
                reject("Verification must execute directly and propagate its exit status")
    if hashlib.sha256(text.encode("utf-8")).hexdigest() != APPROVED_WORKFLOW_SHA256:
        reject("Workflow differs from the complete reviewed workflow digest; a reviewed profile update is required")
    return {"contexts": sorted(JOBS), "publisher_binding": "requires live read-back"}

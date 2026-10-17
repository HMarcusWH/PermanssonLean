"""Review-sensitive structural contract for the three checked-in CI jobs."""
import hashlib
from pathlib import Path
import re
from .git_objects import GitRepo
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

# Review the entire workflow set, not a grep of job names: another YAML file
# can publish a colliding required context through quoted/flow/tagged or dynamic
# forms. Exact set membership and complete canonical-LF payload pins avoid a
# pretend general YAML parser. New/changed workflows require an explicit
# reviewed profile update; additive Lean modules remain governed separately.
# All optional profiles below were read in full: their literal job IDs differ
# from required contexts; only the approved application profile expands a name
# matrix to the two required application contexts. This is candidate-owned
# reviewed configuration, not independent authentication of its own review.
APPROVED_WORKFLOWS = {
    "a2-smoke.yml": "9ac3460a79cf861b43d5329d06a03650cc8c4de09d24cd677849eb1772c73a19",
    "a3-contractive-smoke.yml": "b7e3b723bb25e5287bdd60ee1470fabeeaac318617cca4f9ed1931c5a01c7931",
    "application.yml": "356d62c5e8203ff9cc478f6d5f19d6bccb018eec5c3612b4d30d4b318c8db7e0",
    "b2-smoke.yml": "3204afca3fb58bc72f6c90bfe6ca2b17e06b9b6c2b500b6087ee4c66ca7baebc",
    "c-exit-random-entry-smoke.yml": "499a5c76ecff1ab3b891df24477b249f9809b13201e9cee6b0a84250b3087536",
    "c-exit-restart-d-smoke.yml": "1ae741ce18c04d54bf3a25f82ef29041188551f8472757904b4675b2fbd443c3",
    "c-exit-restart-smoke.yml": "dd2b5cfd181fa3b42d4f998e622762473808c9e90fb72e7b0190f19d6e84e1f3",
    "c-exit-smoke.yml": "a6f5fcbd0c087848c02538f2aebbf4c0bc7cf655dbf4197d366c88f67295eaf7",
    "c-exit-switch-smoke.yml": "5ebe0c3b24621ef2e2e4cfa518a48cca39f4e576e72405122730daca0985a7c4",
    "d2-residence-smoke.yml": "47b95f2477cccb552074eb9168bdc4f28d5d7d456892a9b2ac44959e519d7908",
    "e1-approx-quotient-smoke.yml": "73e09702dd2eb99c5da85d7efa86e6bfdd05b936a71c67b0d8fb4981c3a29ac5",
    "f1-multiagent-protocols-smoke.yml": "475242f86682e23f8924d0f9b5e26db7f35971ee6c7c682cebc24ed6ef62c0ba",
    "lean.yml": "2dc2bc23f6013faed093fbff8238801b0dab1bc6a121c9ea12dc07c99fa20432",
    "research-integrity-portability.yml": "23c0b16125590d19c017a191b1b4a0b41ea8b15063fc13b246352901f64ad43e",
    "research-integrity.yml": APPROVED_WORKFLOW_SHA256,
    "research-lean.yml": "cb676566d9c0867b4b990ff83dffded6927972aca58068c6ab185cdf6af64eca",
    "research-release-verification.yml": "6990c58ca64a260eab301ae022974b2642d80558817def87581087751a83821b",
    "verification.yml": "8ec37551fc4a7b71e24fac0d5ead92ab308c40b4c35fe83f8befec39f14ce302",
    "x1-commons-smoke.yml": "606e8cf1b579f3012f534799e514c372a51e67cef990972718dc1724b206ea2d",
}
LEGACY_CONTEXTS = {"build", "research", "executable-verification",
                   "Application contract (ubuntu-latest)", "Application contract (windows-latest)"}
LEGACY_COMMAND = 'python -B -m verification.integrity.ci_context --repo . --event-file "$GITHUB_EVENT_PATH" --report "$RUNNER_TEMP/required-source.json"'
LEGACY_FIRST_WORK = {
    "lean.yml": "      - uses: leanprover/lean-action@",
    "research-lean.yml": "      - name: Build research library and audit its transitive axioms",
    "verification.yml": "      - name: Install Python dependencies",
    "application.yml": "      - name: Install application-only dependencies",
}


def load_workflows(root=None):
    """Read committed HEAD payloads, never checkout newline conversions.

    The required test runner first binds HEAD to the genuine event and rejects
    dirty CI sources. Untracked files cannot publish a GitHub check; conversely
    a committed CRLF edit is a real profile edit and must not be normalized.
    """
    root = Path(root) if root is not None else Path(__file__).resolve().parents[2]
    repo = GitRepo(root)
    try:
        candidate = repo.run("rev-parse", "HEAD").strip().decode("ascii")
        entries = repo.tree_entries(candidate)
        directory = entries.get(b".github/workflows")
        if directory is None or directory.mode != "040000" or directory.object_type != "tree":
            raise HardeningError("E_WORKFLOW_CONTRACT", "Committed workflow directory is unavailable")
        prefix = b".github/workflows/"
        direct = [entry for path, entry in entries.items()
                  if path.startswith(prefix) and b"/" not in path[len(prefix):]]
        if len(direct) > 128:
            raise HardeningError("E_WORKFLOW_CONTRACT", "Workflow directory exceeds reviewed entry budget")
        result = {}
        for entry in direct:
            name = entry.path[len(prefix):].decode("ascii")
            if not name.lower().endswith((".yml", ".yaml")):
                continue
            if name not in APPROVED_WORKFLOWS or entry.mode != "100644" or entry.object_type != "blob":
                raise HardeningError("E_WORKFLOW_CONTRACT", "Workflow set contains an unreviewed filename/type/mode")
            result[name] = repo.blob(entry.oid, limit=1024 * 1024).decode("utf-8")
        return result
    except (OSError, UnicodeError) as error:
        raise HardeningError("E_WORKFLOW_CONTRACT", "Complete reviewed workflow set is unavailable") from error
    finally:
        repo.close()


def validate_workflow_set(workflows):
    def reject(message):
        raise HardeningError("E_WORKFLOW_CONTRACT", message)
    if not isinstance(workflows, dict) or set(workflows) != set(APPROVED_WORKFLOWS):
        reject("Complete reviewed workflow set has missing or additional files; context-name collision cannot be excluded")
    guard = "      - name: Bind genuine required-check source\n        shell: bash\n        run: " + LEGACY_COMMAND + "\n"
    for name, first_work in LEGACY_FIRST_WORK.items():
        text = workflows[name]
        if not isinstance(text, str):
            reject("Workflow profile must be canonical text")
        if "workflow_dispatch" in text or "pull_request_target" in text:
            reject("Legacy required contexts cannot issue diagnostic/privileged-event success")
        if ("\n  pull_request:\n    branches: [main]\n" not in text
                or "\n  push:\n    branches: [main]\n" not in text):
            reject("Legacy required contexts must run for genuine main PRs and main pushes")
        if (text.count("\npermissions:\n  contents: read\n") != 1
                or text.count("          fetch-depth: 0\n") != 1
                or text.count("          persist-credentials: false\n") != 1):
            reject("Legacy required contexts need a full-history credential-free read-only checkout")
        if (text.count(guard) != 1 or text.count(LEGACY_COMMAND) != 1
                or first_work not in text or text.index(guard) > text.index(first_work)):
            reject("Every legacy required context must directly bind source before proof/tests/dependencies")
        if ('        run: ' + LEGACY_COMMAND + '\n') not in text:
            reject("Legacy source binding must propagate its real exit status")
        if "      - name: Preserve required-check source context\n        if: always()\n" not in text:
            reject("Legacy required contexts must retain their actual source-binding report")
    for name, digest in APPROVED_WORKFLOWS.items():
        text = workflows[name]
        if not isinstance(text, str) or hashlib.sha256(text.encode("utf-8")).hexdigest() != digest:
            reject("Complete reviewed workflow set digest differs: " + name)
    return {"workflows": len(workflows), "legacy_contexts": sorted(LEGACY_CONTEXTS),
            "required_context_names_unique": "reviewed complete payload/set pins; not a YAML grep"}


def validate_workflow(text, workflows=None):
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
    registry = validate_workflow_set(load_workflows() if workflows is None else workflows)
    return {"contexts": sorted(JOBS), "publisher_binding": "requires live read-back", **registry}

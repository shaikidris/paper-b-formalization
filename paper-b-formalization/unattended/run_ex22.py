#!/usr/bin/env python3
"""Run and record the bounded local Carbon queue for Paper B EX2.2."""
from datetime import datetime, timezone
import fcntl
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from uuid import UUID, uuid4

HERE = Path(__file__).resolve().parent
BOARD = HERE.parent
PROJECT = BOARD.parent
RUNTIME = PROJECT / ".collaboration/unattended-ex22"
HOME = Path.home()
ELAN = HOME / ".local/bin/elan"
AGY = HOME / "research/antigravity/cli/agy"
RELAY = HOME / ".codex/skills/research-relay/scripts/consult_antigravity.py"
OWNER = "01a1ef46-200f-7cb1-a352-a1810783a46d"
SESSION = PROJECT / ".collaboration/sessions" / OWNER / "antigravity-files"
NATIVE = "3d729ac9-6887-4757-b9b8-920df3eb58dd"
MODEL = "gemini-4-carbon-medium"
PIN = (BOARD / "release-core/lean-toolchain").read_text().strip()
TOOLCHAIN = HOME / ".elan/toolchains" / PIN.replace("/", "--").replace(":", "---")
LEAN = TOOLCHAIN / "bin/lean"
MODULE = Path("release-core/PaperB/ExitPaths.lean")
GIT = ["git", "--git-dir=evidence/paper-b-editions.git", "--work-tree=."]
STAGES = json.loads((HERE / "ex22-contracts.json").read_text())
FENCE = chr(96) * 3


class Blocked(RuntimeError):
    pass


def now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def read(path):
    return json.loads(path.read_text())


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def atomic(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temp = tempfile.mkstemp(dir=path.parent, prefix=".writing-")
    with os.fdopen(fd, "w", encoding="utf-8") as stream:
        stream.write(text)
    os.replace(temp, path)


def save(path, value):
    atomic(path, json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def call(argv, cwd=PROJECT, timeout=60, env=None):
    try:
        return subprocess.run(argv, cwd=cwd, capture_output=True, text=True,
                              timeout=timeout, env=env)
    except subprocess.TimeoutExpired as error:
        raise Blocked(f"{Path(argv[0]).name} exceeded {timeout} seconds") from error


def checked(argv, cwd=PROJECT):
    result = call(argv, cwd)
    if result.returncode:
        raise Blocked((result.stderr + result.stdout).strip()[-700:])
    return result.stdout.strip()


def git(*args):
    return checked([*GIT, *args])


def clean():
    if git("diff", "--cached", "--name-only") or git("status", "--porcelain", "--", BOARD.name):
        raise Blocked("The Git index or formalization has other changes. Review the checkout before resuming.")


def update(work, status, state, detail):
    status.update(state=state, detail=detail, updated=now())
    save(work / "status.json", status)
    save(RUNTIME / "status.json", status)
    rows = "\n".join(f"| {r['name']} | {r['state']} |" for r in status["stages"])
    atomic(RUNTIME / "STATUS.md", f"""# Paper B EX2.2 unattended run

**{state}** · Updated {status['updated']} · Run {work.name}

{detail}

| Declaration | Progress |
|---|---|
{rows}
""")


def prepare(scratch):
    shutil.copytree(BOARD / "release-core", scratch / "lake", ignore=shutil.ignore_patterns(".lake"))
    checked([str(ELAN), "run", PIN, "lake", "build", "PaperB.ExitPaths"], scratch / "lake")


def lean_check(scratch, text):
    path = scratch / "Check.lean"
    path.write_text(text)
    profile = scratch / "lean.sb"
    profile.write_text("""(version 1)
(allow default)
(deny network*)
(deny file-read-data (require-all (subpath (param "USER_HOME"))
                                (require-not (subpath (param "TOOLCHAIN")))))
(deny file-write* (require-not (subpath (param "SCRATCH"))))
(deny process-fork)
(deny process-exec (require-not (literal (param "LEAN"))))
""")
    env = dict(os.environ, LEAN_PATH=str(scratch / "lake/.lake/build/lib/lean"), TMPDIR=str(scratch))
    return call(["/usr/bin/sandbox-exec", "-D", f"USER_HOME={HOME}", "-D", f"TOOLCHAIN={TOOLCHAIN}",
                 "-D", f"SCRATCH={scratch}", "-D", f"LEAN={LEAN}", "-f", str(profile),
                 str(LEAN), str(path)], scratch, timeout=60, env=env)


def preflight():
    for path in (ELAN, LEAN, AGY, RELAY):
        if not path.is_file():
            raise Blocked(f"Missing required local file {path}")
    session = read(SESSION / "session.json")
    if session["status"] != "ready" or session["provider_conversation_id"] != NATIVE:
        raise Blocked("The existing Carbon conversation has an open or unresolved turn.")
    with tempfile.TemporaryDirectory(prefix="ex22-preflight-", dir="/private/tmp") as tmp:
        scratch = Path(tmp).resolve()
        prepare(scratch)
        # Signature-only scratch declarations are never integrated.
        signatures = "\n\n".join(s["statement"].replace("theorem ", "axiom ", 1) for s in STAGES)
        result = lean_check(scratch, "import PaperB.ExitPaths\nset_option autoImplicit false\n"
                            "namespace PaperB.LabelledQuotient\n" + signatures
                            + "\nend PaperB.LabelledQuotient\n")
        if result.returncode:
            raise Blocked("Scoped Lean preflight failed. " + (result.stderr + result.stdout).strip())


def ask_carbon(work, stage, attempt, feedback, status):
    ready = read(SESSION / "session.json")
    if ready["status"] != "ready" or ready["provider_conversation_id"] != NATIVE:
        raise Blocked("Carbon is busy or the previous conversation needs review.")
    target = work / "relay" / str(uuid4())
    target.parent.mkdir(exist_ok=True)
    prompt = work / f"{stage['id']}-{attempt}.md"
    atomic(prompt, f"""Paper B v1.2, EX2.2, {stage['id']}. Give one Lean proof in PaperB.LabelledQuotient, importing the existing PaperB.ExitPaths, using Lean {PIN}. Write 0001.md immediately with one fenced lean declaration and one short progress line. Use the exact theorem header including binder names. If correcting the file, write the replacement in the next numbered checkpoint. Seal with COMPLETE. If blocked, report the exact missing step. No commands, imports, new definitions, metaprogramming, placeholders, or other files.

{stage['statement']} := by

{stage['hint']}

{feedback}
""")
    update(work, status, "WAITING_FOR_CARBON", f"{stage['id']} · attempt {attempt}")
    args = [sys.executable, "-B", str(RELAY), "--executable", str(AGY), "--session-owner", OWNER,
            "--model", MODEL, "--effort", "medium", "--report-mode", "files", "--timeout-seconds", "420",
            "--prompt-file", str(prompt), "--output-dir", str(target)]
    with (work / f"{stage['id']}-{attempt}.relay.log").open("w") as log:
        process = subprocess.Popen(args, cwd=PROJECT, stdout=log, stderr=subprocess.STDOUT)
        saved_count, sealed_at = 0, None
        deadline = time.monotonic() + 450
        while process.poll() is None:
            files = target / "checkpoints"
            count = len(list(files.glob("[0-9][0-9][0-9][0-9].md")))
            if count != saved_count:
                saved_count = count
                update(work, status, "CHECKPOINT_SAVED", f"{stage['id']} · {count} saved checkpoint(s)")
            if (files / "COMPLETE").is_file():
                sealed_at = sealed_at or time.monotonic()
            if time.monotonic() > deadline or (sealed_at and time.monotonic() - sealed_at > 30):
                process.send_signal(signal.SIGINT)
                process.wait(timeout=15)
                break
            time.sleep(2)
    receipt_file = target / "receipt.json"
    if not receipt_file.is_file():
        raise Blocked(f"The relay did not write a receipt. See {target.relative_to(PROJECT)}")
    receipt = read(receipt_file)
    if (receipt.get("provider_reported_model") != MODEL or receipt.get("provider_conversation_id") != NATIVE
            or receipt.get("session_error") or receipt.get("forbidden_tool_steps") != 0
            or not receipt.get("inputs_unchanged") or receipt.get("unexpected_workspace_paths")):
        raise Blocked(f"Carbon's delivery failed the session or output checks. See {receipt_file.relative_to(PROJECT)}")
    sections = receipt.get("report_files", {}).get("sections", [])
    if not sections or receipt.get("report_state") not in {"complete", "partial"}:
        raise Blocked(f"Carbon ended without saving proof files. See {receipt_file.relative_to(PROJECT)}")
    return receipt_file, receipt, target / "checkpoints" / sections[-1]


def candidate(stage, checkpoint, base):
    text = checkpoint.read_text()
    blocks = re.findall(rf"^{FENCE}lean[ \t]*\n(.*?)^{FENCE}[ \t]*$", text, re.S | re.M)
    if len(blocks) != 1:
        raise Blocked("Carbon did not save one Lean declaration. " + " ".join(text.split())[:220])
    head, boundary, body = blocks[0].strip().partition(":= by")
    if not boundary or head.split() != stage["statement"].split():
        raise Blocked("The checkpoint changed its pinned declaration header.")
    deny = r"#|«|»|/[-]|--|\b(sorry|admit|axiom|unsafe|native_decide|run_tac|run_cmd|elab|macro|syntax|set_option|import|initialize|open|namespace|end|theorem|lemma|def|abbrev|opaque|attribute|section|universe|module|IO|System|Lean|trace_state)\b"
    if (not body.startswith("\n") or any(line and not line[0].isspace() for line in body.splitlines())
            or re.search(deny, body) or len(body.encode()) > 30000):
        raise Blocked("The proof must be an indented tactic block without commands, placeholders, or metaprogramming.")
    marker = "\nend LabelledQuotient\n"
    if base.count(marker) != 1 or re.search(rf"^theorem {stage['name']}\b", base, re.M):
        raise Blocked("The intended namespace or insertion point changed.")
    note = re.sub(rf"^{FENCE}lean[ \t]*\n.*?^{FENCE}[ \t]*$", "", text, flags=re.S | re.M).strip()
    return base.replace(marker, f"\n{stage['statement']} := by{body}\n" + marker), note[:500]


def recover(receipt_file, receipt):
    if receipt["transport_status"] == "returned":
        return
    if receipt["transport_status"] not in {"cancelled", "timed_out"}:
        raise Blocked("Carbon transport needs review before another turn.")
    with (SESSION / "session.lock").open("r+") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        path = SESSION / "session.json"
        state = read(path)
        if (state["status"] != "needs_review" or state["provider_conversation_id"] != NATIVE
                or state.get("last_receipt") != str(receipt_file)
                or state.get("active_output") != str(receipt_file.parent)):
            raise Blocked("Carbon's saved session no longer matches the verified checkpoint.")
        review = receipt_file.parent / "checked-recovery.json"
        save(review, dict(previous=state, reason="The saved declaration passed the pinned Lean check."))
        state.pop("active_output")
        state.update(status="ready", reviewed_recovery=str(review), updated_at=now())
        save(path, state)


def update_tracker(work, status, message, extra=()):
    path = BOARD / "tasks.json"
    data = read(path)
    task = next(t for t in data["tasks"] if t["id"] == "EX2.2")
    task.setdefault("dispatch", {})["unattended"] = {
        "run": work.name, "state": status["state"], "checked": status["completed"]}
    task["progress"] = message
    for file in extra:
        if file.suffix == ".json":
            task["evidence"].append(file.relative_to(BOARD).as_posix())
    save(path, data)
    event_file = BOARD / "events.jsonl"
    with event_file.open("a") as file:
        file.write(json.dumps(dict(at=now(), kind="EX22_UNATTENDED", task="EX2.2", run=work.name,
                                   state=status["state"], detail=message)) + "\n")
    checked([sys.executable, "-B", str(BOARD / "plan.py"), "render"])
    manifest = BOARD / "artifact-manifest.json"
    doc = read(manifest)
    items = sorted(p for p in BOARD.rglob("*") if p.is_file()
                   and p.name not in {".DS_Store", manifest.name}
                   and not {".lake", ".git", "__pycache__"}.intersection(p.relative_to(BOARD).parts))
    doc["files"] = [dict(path=p.relative_to(BOARD).as_posix(), bytes=p.stat().st_size, sha256=digest(p))
                    for p in items]
    save(manifest, doc)
    files = [*extra, *(BOARD / name for name in ("tasks.json", "events.jsonl", "artifact-manifest.json",
                                                 "DASHBOARD.md", "TASKS.md"))]
    paths = [p.relative_to(PROJECT).as_posix() for p in files]
    git("diff", "--check", "--", *paths)
    git("add", "--", *paths)
    return git("commit", "--only", "-m", f"Record EX2.2 unattended {status['state'].lower()}",
               "--", *paths).splitlines()[0]


def stage_run(work, stage, row, status):
    module = BOARD / MODULE
    base = module.read_text()
    feedback = ""
    with tempfile.TemporaryDirectory(prefix="ex22-lean-", dir="/private/tmp") as tmp:
        scratch = Path(tmp).resolve()
        prepare(scratch)
        for attempt in (1, 2):
            receipt_file, receipt, checkpoint = ask_carbon(work, stage, attempt, feedback, status)
            update(work, status, "CHECKING", f"Checking {stage['name']} with the pinned Lean build.")
            log = work / f"{stage['id']}-{attempt}.lean.txt"
            try:
                full_source, note = candidate(stage, checkpoint, base)
                name = "PaperB.LabelledQuotient." + stage["name"]
                result = lean_check(scratch, full_source + f"\n#check {name}\n#print axioms {name}\n")
                output = result.stdout + result.stderr
                atomic(log, output)
                dependencies = [line for line in output.splitlines() if line.startswith(f"'{name}'")]
                if result.returncode or len(dependencies) != 1 or "axioms" not in dependencies[0]:
                    raise Blocked("The exact Lean declaration did not build.")
                dependency = dependencies[0]
                allowed = {"propext", "Quot.sound", "Classical.choice"}
                if "[" in dependency and not set(dependency.partition("[")[2].rstrip("]").split(", ")).issubset(allowed):
                    raise Blocked("The declaration depends on an unapproved axiom.")
            except Blocked as error:
                if attempt == 2 or status["repair_used"] or receipt["transport_status"] != "returned":
                    evidence = log if log.exists() else receipt_file
                    raise Blocked(f"{error} See {evidence.relative_to(PROJECT)}") from error
                status["repair_used"] = True
                details = log.read_text() if log.exists() else str(error)
                diagnostic = details.replace(str(scratch), "<scratch>")[-2400:]
                feedback = "Repair the same declaration using this local diagnostic.\n\n" + diagnostic
                continue
            clean()
            if module.read_text() != base:
                raise Blocked("The target module changed during validation.")
            atomic(module, full_source)
            evidence = BOARD / "evidence/ex22-unattended" / f"{work.name}-{stage['id']}.json"
            save(evidence, dict(run=work.name, name=name, toolchain=PIN, worker="Gemini 4 Carbon Medium",
                                statement=stage["statement"], note=note, dependencies=dependency,
                                checkpoint=checkpoint.relative_to(PROJECT).as_posix(), checkpoint_sha256=digest(checkpoint),
                                receipt=receipt_file.relative_to(PROJECT).as_posix(), receipt_sha256=digest(receipt_file),
                                build_log=log.relative_to(PROJECT).as_posix(), source_sha256=digest(module)))
            status["completed"].append(stage["id"])
            row["state"] = "BUILT"
            update(work, status, "BUILT_CHECKPOINT", f"{name} passed Lean.")
            message = (f"{len(status['completed'])} of 3 unattended declarations build. "
                       "Full finite-sweep construction and statement-level review remain open.")
            status["commits"].append(update_tracker(work, status, message, (module, evidence)))
            recover(receipt_file, receipt)
            return
    raise Blocked("The repair budget was exhausted.")


def notify(state, message):
    source = """on run argv
display notification (item 2 of argv) with title (item 1 of argv)
end run"""
    result = call(["/usr/bin/osascript", "-e", source, f"Paper B EX2.2 {state.lower()}", message[:260]], timeout=20)
    return dict(request_accepted=result.returncode == 0, detail=result.stderr.strip()[:300])


def run(run_id):
    RUNTIME.mkdir(parents=True, exist_ok=True)
    with (RUNTIME / "runner.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        work = RUNTIME / str(UUID(run_id))
        work.mkdir()
        status = dict(run=work.name, started=now(), completed=[], commits=[], repair_used=False,
                      stages=[dict(name=s["name"], state="QUEUED") for s in STAGES])
        outcome, current = "BUILT", "preflight"
        try:
            update(work, status, "STARTING", "Checking the existing Carbon session and Lean toolchain.")
            clean()
            preflight()
            for stage, row in zip(STAGES, status["stages"]):
                current = stage["id"]
                row["state"] = "IN_PROGRESS"
                stage_run(work, stage, row, status)
            message = ("The predecessor prefix, pair-key parent reuse, and the sweep induction transition "
                       "build. The full finite-sweep construction and statement-level review remain open.")
        except Exception as error:
            outcome = "BLOCKED"
            for row in status["stages"]:
                if row["state"] == "IN_PROGRESS":
                    row["state"] = outcome
            message = f"Stopped at {current} after {len(status['completed'])} of 3 declarations. {error}"
        update(work, status, outcome, message)
        try:
            clean()
            status["commits"].append(update_tracker(work, status, message))
        except Exception as error:
            outcome = "BLOCKED"
            message += " The tracker commit needs review. " + str(error)[:240]
        try:
            status["notification"] = notify(outcome, message)
        except Exception as error:
            status["notification"] = dict(request_accepted=False, detail=str(error)[:240])
        update(work, status, outcome, message)
        print(message, flush=True)
        return 0 if outcome == "BUILT" else 1


if __name__ == "__main__":
    if sys.argv[1:] == ["--check"]:
        preflight()
        print("Preflight passed for the Carbon session, sandboxed Lean, and three exact declarations.")
    elif len(sys.argv) == 3 and sys.argv[1] == "--run":
        sys.exit(run(sys.argv[2]))
    else:
        sys.exit("Usage: run_ex22.py --check | --run RUN_UUID")

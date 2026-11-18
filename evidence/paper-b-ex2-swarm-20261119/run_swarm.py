#!/usr/bin/env python3
"""Dispatch Paper B EX2 to parallel Carbon Medium file-report workers."""
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
from threading import Lock
import time
from uuid import UUID, uuid4

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
BOARD = PROJECT / "paper-b-formalization"
sys.path.insert(0, str(BOARD / "unattended"))
import run_ex22 as base

RUNTIME = PROJECT / ".collaboration/unattended-ex2-swarm"
OWNER = "01a1ef46-200f-7cb1-a352-a1810783a46d"
MODEL = "gemini-4-carbon-medium"
FENCE = chr(96) * 3
LOCK = Lock()
LANES = json.loads((HERE / "lanes.json").read_text())

def context():
    manuscript = PROJECT / "submissions/paper-b-v1.3-20261118/paper-b-v1.3.md"
    text = manuscript.read_text()
    forest = text[text.index("## 3. A forest"):text.index("## 4. Transferring")]
    source = (BOARD / "release-core/PaperB/ExitPaths.lean").read_text()
    headers = [part.partition(" := by")[0] for part in source.split("\ntheorem ")[1:]]
    contracts = json.loads((BOARD / "unattended/ex22-contracts.json").read_text())
    return {
        "paper_sha": sha256(manuscript.read_bytes()).hexdigest(),
        "core_sha": sha256(source.encode()).hexdigest(),
        "forest": forest,
        "available": "\n\n".join("theorem " + h.strip() for h in headers),
        "sweep_contracts": "\n\n".join(s["statement"] for s in contracts),
    }

class Run:
    def __init__(self, run_id):
        self.work = RUNTIME / str(UUID(run_id))
        self.work.mkdir()
        self.state = {
            "run": self.work.name, "goal": "EX2 Pair Forest, Lemmas 3.1 and 3.2 of Paper B v1.3",
            "model": MODEL, "max_concurrency": 2, "state": "RUNNING",
            "lanes": {d["id"]: {"state": "QUEUED", "tasks": d["tasks"], "files": 0} for d in LANES},
        }
        self.frozen = context()
        base.save(self.work / "source-snapshot.json", self.frozen)
        self.write()

    def write(self):
        self.state["updated_at"] = base.now()
        base.save(self.work / "status.json", self.state)
        base.save(RUNTIME / "status.json", self.state)
        rows = "\n".join(
            f"| {k} | {d['tasks']} | {d['state']} | {d['files']} |"
            for k, d in self.state["lanes"].items()
        )
        detail = "\n".join(f"- **{k}** {d['detail']}" for k, d in self.state["lanes"].items() if d.get("detail"))
        base.atomic(RUNTIME / "STATUS.md",
                    f"# Paper B EX2 Pair Forest\n\n**{self.state['state']}** · "
                    f"{self.state['updated_at']} · Run {self.work.name}\n\n"
                    "Results are checked as candidate modules. The milestone closes after integration and exact statement review.\n\n"
                    "| Lane | Tasks | State | Saved files |\n|---|---|---|---|\n" + rows + "\n\n" + detail + "\n")

    def update(self, lane, **fields):
        with LOCK:
            self.state["lanes"][lane].update(fields)
            self.write()

    def packet(self, lane):
        snapshots = {
            k: {"state": row["state"], "module": row.get("module"), "declarations": row.get("declarations", [])}
            for k, row in self.state["lanes"].items()
        }
        other = []
        for k, v in snapshots.items():
            if k != lane["id"] and v["state"] == "CANDIDATE_BUILDS":
                file = self.work / k / "candidate.lean"
                if file.is_file():
                    other.append(f"Checked in scratch by sibling lane {k}:\n{file.read_text()[:18000]}")
        return f"""One full milestone is assigned to Carbon Medium: Paper B v1.3 EX2 Pair Forest. Your lane is {lane['id']} ({lane['tasks']}). The other lanes independently handle the other parts. Your goal is a complete Lean proof or implementation of your lane, with a precise blocker if full proof is still pending.

{lane['acceptance']}

Write progress into numbered Markdown checkpoint files as work proceeds. Start promptly with the declaration contract and first concrete proof. At every independently useful result, add a status line naming what is checked by reasoning and what remains. Put the newest self-contained Lean MODULE BODY in one fenced lean block in the last code checkpoint, omitting imports, namespace wrappers, and file-level options. The local runner inserts import PaperB.ExitPaths and opens PaperB.LabelledQuotient in namespace PaperB.{lane['module']}. Do not use placeholders, custom axioms, metaprogramming, tools other than file creation, or shell commands. Use qualified names for library lemmas where needed. Set COMPLETE to the number of report files. If no complete code can be supplied, save the exact first unproved obligation instead. Any conditional theorem must list its hypotheses and the missing bridge.

Frozen published Markdown SHA-256 {self.frozen['paper_sha']}. The current Lean pin is {base.PIN}. Available checked declarations at launch, from ExitPaths SHA-256 {self.frozen['core_sha']}:

{self.frozen['available']}

The ongoing sequential worker owns the local sweep transition. These are its pinned contracts. If a declaration is absent from the checked list above, its availability is pending; do not mark it proved inside your module. Specialize or parameterize your own global proof as needed.

{self.frozen['sweep_contracts']}

{chr(10).join(other)}

Exact source for the target milestone follows.

{self.frozen['forest']}
"""

    def consult(self, lane):
        ident = lane["id"]
        folder = self.work / ident
        folder.mkdir()
        output = folder / "delivery" / str(uuid4())
        output.parent.mkdir()
        request = folder / "request.md"
        base.atomic(request, self.packet(lane))
        session = RUNTIME / "sessions" / ident
        args = [sys.executable, "-B", str(base.RELAY), "--executable", str(base.AGY),
                "--session-owner", OWNER, "--session-dir", str(session),
                "--model", MODEL, "--effort", "medium", "--report-mode", "files",
                "--timeout-seconds", "720", "--prompt-file", str(request), "--output-dir", str(output)]
        self.update(ident, state="WAITING_FOR_CARBON", delivery=output.relative_to(PROJECT).as_posix())
        with (folder / "relay.log").open("w") as log:
            proc = subprocess.Popen(args, cwd=PROJECT, stdout=log, stderr=subprocess.STDOUT)
            count = 0
            sealed = None
            end = time.monotonic() + 750
            while proc.poll() is None:
                checkpoints = output / "checkpoints"
                files = sorted(checkpoints.glob("[0-9][0-9][0-9][0-9].md"))
                if len(files) != count:
                    count = len(files)
                    last = files[-1].read_text(errors="replace").splitlines()
                    note = next((line for line in last[:6] if line.strip() and not line.startswith(FENCE)), "")
                    self.update(ident, state="CHECKPOINT_SAVED", files=count, detail=note.replace("|", "/")[:240])
                if (checkpoints / "COMPLETE").is_file():
                    sealed = sealed or time.monotonic()
                if time.monotonic() > end or (sealed and time.monotonic() - sealed > 30):
                    proc.send_signal(signal.SIGINT)
                    proc.wait(timeout=15)
                    break
                time.sleep(2)
        receipt = base.read(output / "receipt.json")
        sections = receipt.get("report_files", {}).get("sections", [])
        if (receipt.get("provider_reported_model") != MODEL or receipt.get("session_error")
                or receipt.get("forbidden_tool_steps") != 0 or not receipt.get("inputs_unchanged")
                or receipt.get("unexpected_workspace_paths")
                or receipt.get("report_state") not in {"complete", "partial"} or not sections):
            raise base.Blocked("Delivery ended without a usable checked-scope checkpoint. See relay.log and receipt.json.")
        self.update(ident, state="CHECKING", files=len(sections), detail="Checking the newest saved Lean candidate.")
        self.verify(lane, folder, output, receipt, sections)

    def verify(self, lane, folder, output, receipt, sections):
        code = None
        for name in reversed(sections):
            file = output / "checkpoints" / name
            blocks = re.findall(rf"^{FENCE}lean[ \t]*\n(.*?)^{FENCE}[ \t]*$", file.read_text(), re.M | re.S)
            if len(blocks) == 1:
                code = blocks[0].strip()
                selected = name
                break
        if not code:
            raise base.Blocked("Carbon recorded progress or a blocker without a complete Lean module body. See the saved report.")
        deny = r"#|«|»|\b(sorry|admit|unsafe|axiom|native_decide|run_tac|run_cmd|elab|macro|syntax|set_option|import|initialize|open|namespace|end|IO|System|Lean)\b"
        comment_free = re.sub(r"/-.*?-/", "", code, flags=re.S)
        comment_free = re.sub(r"--[^\n]*", "", comment_free)
        if re.search(deny, comment_free):
            raise base.Blocked("The candidate uses an unsupported command or proof placeholder. The report is preserved.")
        names = re.findall(r"^(?:theorem|lemma)\s+([\w.']+)", comment_free, re.M)
        if not names:
            raise base.Blocked("The module has no public theorem to check.")
        namespace = "PaperB." + lane["module"]
        source = ("import PaperB.ExitPaths\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\n"
                  f"namespace {namespace}\nopen PaperB.LabelledQuotient\n\n{code}\n\nend {namespace}\n")
        base.atomic(folder / "candidate.lean", source)
        audit = "\n".join(f"#check {namespace}.{n}\n#print axioms {namespace}.{n}" for n in names)
        with tempfile.TemporaryDirectory(prefix="ex2-swarm-build-", dir="/private/tmp") as tmp:
            scratch = Path(tmp).resolve()
            base.prepare(scratch)
            result = base.lean_check(scratch, source + "\n" + audit + "\n")
        log = result.stdout + result.stderr
        base.atomic(folder / "build.txt", log)
        if result.returncode:
            raise base.Blocked("Scoped Lean elaboration failed. The full diagnostic is in build.txt.")
        dependencies = [line for line in log.splitlines()
                        if any(line.startswith(f"'{namespace}.{n}'") and "axioms" in line for n in names)]
        if len(dependencies) != len(names):
            raise base.Blocked("Axiom reports are incomplete. See build.txt.")
        for line in dependencies:
            if "[" in line and not set(line.partition("[")[2].rstrip("]").split(", ")).issubset(
                {"propext", "Quot.sound", "Classical.choice"}
            ):
                raise base.Blocked("Candidate depends on an unexpected axiom. See build.txt.")
        review = dict(module=namespace, declarations=names, axioms=dependencies,
                      report_state=receipt["report_state"], checkpoint=selected,
                      source_sha256=sha256(source.encode()).hexdigest(),
                      scope="Scratch build. Full statement fidelity and integration are pending.")
        base.save(folder / "verification.json", review)
        self.update(lane["id"], state="CANDIDATE_BUILDS", module=namespace, declarations=names,
                    detail=f"{len(names)} theorem(s) build in scratch. Integration and exact statement review are pending.")

    def worker(self, lane):
        try:
            self.consult(lane)
        except Exception as error:
            self.update(lane["id"], state="NEEDS_REVIEW", detail=str(error)[:350])

    def execute(self):
        with ThreadPoolExecutor(max_workers=2) as pool:
            list(pool.map(self.worker, LANES))
        self.state["state"] = (
            "READY_FOR_INTEGRATION" if all(d["state"] == "CANDIDATE_BUILDS" for d in self.state["lanes"].values())
            else "CHECKPOINTS_NEED_REVIEW"
        )
        self.write()
        count = sum(d["state"] == "CANDIDATE_BUILDS" for d in self.state["lanes"].values())
        message = f"EX2 Carbon swarm returned. {count} of 3 candidate modules build. See the live status for scope and blockers."
        script = """on run argv
display notification (item 1 of argv) with title "Paper B EX2"
end run"""
        result = base.call(["/usr/bin/osascript", "-e", script, message], timeout=20)
        self.state["notification_request_accepted"] = result.returncode == 0
        self.write()

if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit("Usage: run_swarm.py RUN_UUID")
    RUNTIME.mkdir(parents=True, exist_ok=True)
    import fcntl
    with (RUNTIME / "swarm.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        Run(sys.argv[1]).execute()

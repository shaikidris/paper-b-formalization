#!/usr/bin/env python3
"""Local Paper B planning ledger: validation and generated views, not proof checking."""
from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parent
STATUSES = {"PLANNED", "READY", "IN_PROGRESS", "IMPLEMENTED", "VERIFIED", "BLOCKED", "DEFERRED", "DONE_PLAN"}
CLOSED = {"DONE_PLAN", "VERIFIED"}
PATTERN = re.compile(r"^\*\*(Lemma|Proposition|Theorem|Corollary|Question)\s+([A-Z0-9]+\.\d+)\s*\(([^\n]*?)\)\.\*\*", re.M)


class PlanError(ValueError):
    pass


def need(condition, message):
    if not condition:
        raise PlanError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def load():
    return tuple(read_json(ROOT / n) for n in ("tasks.json", "coverage.json", "obligations.json", "external-inputs.json"))


def validate_records(data, coverage, obligations, external):
    """Validate one supplied snapshot, also used unchanged by negative controls."""
    tasks = data["tasks"]
    ids = [t["id"] for t in tasks]
    need(len(ids) == len(set(ids)), "duplicate task ID")
    index = {t["id"]: t for t in tasks}
    mids = [m["id"] for m in data["milestones"]]
    need(len(mids) == len(set(mids)), "duplicate milestone ID")
    entries = {e["id"]: e for e in coverage["entries"]}
    need(len(entries) == len(coverage["entries"]) == data["manuscript"]["expected_numbered_items"], "wrong active manuscript inventory size")
    need(sum(e["kind"] == "Question" for e in entries.values()) == 1, "expected one open question")
    for t in tasks:
        tid = t["id"]
        need(t["milestone"] in mids, f"{tid}: unknown milestone")
        need(t["status"] in STATUSES, f"{tid}: unknown task status")
        need(t["acceptance"] and t["obligation"], f"{tid}: missing acceptance contract")
        need(t["owner_role"] == data["module_owners"].get(t["planned_owner_module"]), f"{tid}: module owner conflict")
        for dep in t["dependencies"]:
            need(dep in index, f"{tid}: unknown dependency {dep}")
        for consumer in t["paper_consumers"]:
            need(consumer in entries or consumer in {"E.1", "E.2"}, f"{tid}: unknown paper consumer {consumer}")
            need(consumer != "6.2", f"{tid}: open question must not be a proof consumer")
        if t["status"] == "DONE_PLAN":
            need(t["milestone"] == "PB0" and t["proof_status"] == "PLANNING_ONLY", f"{tid}: DONE_PLAN is not proof acceptance")
            need(t["evidence"], f"{tid}: missing planning evidence")
        if t["status"] == "VERIFIED":
            v = t.get("verification", {})
            required = {"source_manifest", "build", "axioms", "fidelity", "dependencies"}
            need(required.issubset(v), f"{tid}: verification record required; a task label is not proof evidence")
            need(t["proof_status"] == "CERTIFIED", f"{tid}: verified proof status mismatch")
        if t["status"] in {"READY", "VERIFIED", "DONE_PLAN"}:
            need(all(index[d]["status"] in CLOSED for d in t["dependencies"]), f"{tid}: incomplete dependencies for {t['status']}")
    visiting, visited = set(), set()

    def visit(tid):
        need(tid not in visiting, f"dependency cycle at {tid}")
        if tid in visited:
            return
        visiting.add(tid)
        for dep in index[tid]["dependencies"]:
            visit(dep)
        visiting.remove(tid)
        visited.add(tid)
    for tid in ids:
        visit(tid)
    for e in entries.values():
        if e["kind"] == "Question":
            need(e["id"] == "6.2" and not e["tasks"] and e["formal_status"] == "OPEN_RESEARCH", "open question incorrectly assigned or certified")
        else:
            need(e["tasks"], f"{e['id']}: uncovered paper statement")
        for tid in e["tasks"]:
            need(tid in index and e["id"] in index[tid]["paper_consumers"], f"{e['id']}: invalid coverage task {tid}")
        if e["formal_status"] == "CERTIFIED":
            need(all(index[x]["status"] == "VERIFIED" for x in e["tasks"]), f"{e['id']}: certification without verified tasks")
    oids = [o["id"] for o in obligations["obligations"]]
    need(len(oids) == len(set(oids)), "duplicate root obligation")
    for o in obligations["obligations"]:
        need(o["paper_root"] in {"3.2", "3.3"}, f"{o['id']}: unapproved selected root")
        need(o["tasks"] and all(x in index for x in o["tasks"]), f"{o['id']}: unknown obligation task")
        if o["status"] == "CLOSED":
            need(o["exact_type"] and o["evidence"] and all(index[x]["status"] == "VERIFIED" for x in o["tasks"]), f"{o['id']}: unsupported obligation closure")
    for o in obligations.get("extension_obligations", []):
        need(o["paper_root"] in entries and all(x in index for x in o["tasks"]), f"{o['id']}: invalid extension obligation")
        if o["status"] == "CLOSED":
            need(o["exact_type"] and o["evidence"] and all(index[x]["status"] == "VERIFIED" for x in o["tasks"]), f"{o['id']}: unsupported extension closure")
    for x in external["inputs"]:
        need(x["consumers"] and all(tid in index for tid in x["consumers"]), f"{x['id']}: unknown external-input consumer")
    need(data["formal_roots_accepted"] == sum(e["formal_status"] == "CERTIFIED" for e in entries.values()), "certified root count does not match coverage")
    return index


def validate_module_graph(data, graph):
    modules = {m["path"]: m for m in graph["modules"]}
    need(len(modules) == len(graph["modules"]), "duplicate planned module")
    for path, module in modules.items():
        need(module["owner_role"] == data["module_owners"].get(path), f"{path}: planned module owner conflict")
        need(all(x in modules for x in module["local_imports"]), f"{path}: unknown local import")
        if path.endswith("/Challenge.lean"):
            need(not module["local_imports"], "Challenge has project import")
    seen, visiting = set(), set()
    def visit(path):
        need(path not in visiting, f"local module import cycle at {path}")
        if path in seen:
            return
        visiting.add(path)
        for dep in modules[path]["local_imports"]:
            visit(dep)
        visiting.remove(path)
        seen.add(path)
    for path in modules:
        visit(path)
    first = {p for p, m in modules.items() if m["admission"] == "FIRST_3_2"}
    reachable = set()
    def reach(path):
        need(path in first, f"first root imports an unadmitted module: {path}")
        if path in reachable:
            return
        reachable.add(path)
        for dep in modules[path]["local_imports"]:
            reach(dep)
    for root in graph["first_roots"]:
        reach(root)
    need(first == reachable, "unreachable planned first-release module")
    need(len(first) <= 18, "proposed module review threshold exceeded")
    return {"planned_first_release_modules":len(first), "planned_unreachable_modules":len(first-reachable), "actual_proof_modules_created":sum((ROOT/p).exists() for p in modules)}


def validate_files(data, coverage):
    validate_module_graph(data, read_json(ROOT / "module-graph.json"))
    lock = read_json(ROOT / "sources/source-lock.json")
    for item in lock["source_files"]:
        file = ROOT / item["path"]
        need(file.is_file() and digest(file.read_bytes()) == item["sha256"], f"pinned source mismatch: {item['path']}")
    for item in lock.get("canonical_files", []):
        file = PROJECT / item["path"]
        need(file.is_file() and digest(file.read_bytes()) == item["sha256"], f"canonical published source mismatch: {item['path']}")
    need(data["manuscript"]["sha256"] == lock["active_sha256"], "tracker active-source identity mismatch")
    need(data["manuscript"]["revision"] == lock["paper_version"] and data["manuscript"]["canonical_path"] == lock["active_canonical_path"] and data["manuscript"]["status"] == lock["publication_status"] and coverage["paper_version"] == lock["paper_version"], "tracker active-source version/status mismatch")
    source = (ROOT / lock["active_source_path"]).read_text()
    need(digest(source.encode()) == lock["active_sha256"], "active source identity mismatch")
    need(digest(source.encode()) == coverage["paper_sha256"], "coverage paper identity mismatch")
    matches = list(PATTERN.finditer(source))
    need([m.group(2) for m in matches] == [e["id"] for e in coverage["entries"]], "paper statement order or inventory mismatch")
    for m, e in zip(matches, coverage["entries"]):
        statement = e["statement"]
        need(source.startswith(statement, m.start()), f"{e['id']}: literal statement mismatch")
        need(e["source_line"] == source.count('\n', 0, m.start()) + 1, f"{e['id']}: source line mismatch")
        need(digest(statement.encode()) == e["statement_sha256"], f"{e['id']}: statement hash mismatch")
        end = m.start() + len(statement) if e["kind"] == "Question" else source.find('∎', m.end()) + 1
        need(end > m.start() and digest(source[m.start():end].encode()) == e["statement_and_proof_sha256"], f"{e['id']}: statement/proof block hash mismatch")
    for item in read_json(ROOT / "sources/authority-retrieval.json")["records"]:
        if "path" in item:
            need(digest((ROOT / item["path"]).read_bytes()) == item["sha256"], f"authority record identity mismatch: {item['id']}")
    for item in read_json(ROOT / "reuse-audit.json")["protected_files"]:
        need(digest((PROJECT / item["path"]).read_bytes()) == item["sha256"], f"legacy source changed since audit: {item['path']}")
    for t in data["tasks"]:
        for path in t["evidence"]:
            need((ROOT / path).is_file(), f"{t['id']}: missing evidence file {path}")
        if t["status"] == "VERIFIED":
            for key, path in t["verification"].items():
                need((ROOT / path).is_file(), f"{t['id']}: missing verification artifact {key}")
    # This checks only ledger integrity. It does not execute a Lean checker or authenticate a future proof report.


def task_ready(data):
    index = {t["id"]: t for t in data["tasks"]}
    return [t for t in data["tasks"] if t["status"] in {"PLANNED", "READY"} and all(index[d]["status"] in CLOSED for d in t["dependencies"])]


def summary(data, coverage, obligations):
    return {
        "source": f"Paper B {data['manuscript']['revision']} (unpublished draft; public base DOI 10.5281/zenodo.24142496)",
        "milestones": len(data["milestones"]),
        "tasks": len(data["tasks"]),
        "task_status_counts": dict(sorted(Counter(t["status"] for t in data["tasks"]).items())),
        "paper_items": len(coverage["entries"]),
        "proof_bearing_items": sum(e["kind"] != "Question" for e in coverage["entries"]),
        "open_questions": [e["id"] for e in coverage["entries"] if e["kind"] == "Question"],
        "certified_new_roots": data["formal_roots_accepted"],
        "selected_root_obligations": dict(sorted(Counter(o["status"] for o in obligations["obligations"]).items())),
        "extension_obligations": dict(sorted(Counter(o["status"] for o in obligations.get("extension_obligations",[])).items())),
        "assigned_workers": sum(t["assigned_agent"] is not None for t in data["tasks"]),
        "dependency_ready": [t["id"] for t in task_ready(data)],
        "execution_status": data["execution_status"],
    }


def cell(value):
    return str(value).replace('|', r'\|').replace('\n', ' ')


def render(data, coverage, obligations, external):
    s = summary(data, coverage, obligations)
    out = ["# Paper B formalization milestones", "", "Generated from tasks.json. Milestone numbers group work; dependencies determine order. Planning completion is separate from proof acceptance.", ""]
    for m in data["milestones"]:
        ts = [t for t in data["tasks"] if t["milestone"] == m["id"]]
        out += [f"## {m['id']} — {m['title']}", "", m["exit_gate"], "", f"Work packages: {len(ts)}; planning audits complete: {sum(t['status']=='DONE_PLAN' for t in ts)}; verified proof packages: {sum(t['status']=='VERIFIED' for t in ts)}.", "", "| Task | Owner | Status | Prerequisites |", "|---|---|---|---|"]
        out += [f"| [{t['id']}](TASKS.md#{t['id'].lower().replace('.', '')}) — {cell(t['title'])} | {t['owner_role']} | {t['status']} | {', '.join(t['dependencies']) or 'none'} |" for t in ts]
        out += [""]
    (ROOT / "MILESTONES.md").write_text('\n'.join(out)+'\n')
    out = ["# Paper B task tracker", "", "Generated from tasks.json. Owner roles are proposed responsibilities, not active agents. Acceptance means exact theorem fidelity and required evidence, not a file count.", ""]
    for t in data["tasks"]:
        out += [f'<a id="{t["id"].lower().replace(".", "")}"></a>', "", f"## {t['id']} — {t['title']}", "", f"- Milestone: {t['milestone']}; status: **{t['status']}**; proof status: {t['proof_status']}.", f"- Owner: {t['owner_role']}; reviewers: {', '.join(t['reviewer_roles']) or 'to assign'}; assigned worker: {t['assigned_agent'] or 'unassigned'}.", f"- Dependencies: {', '.join(t['dependencies']) or 'none'}.", f"- Proposed owner module: `{t['planned_owner_module']}`.", f"- Paper consumers: {', '.join(t['paper_consumers'])}; risk: {t['risk']}.", "", t['obligation'], "", "Acceptance:", ""]
        out += [f"- {a}" for a in t["acceptance"]]
        if t['evidence']:
            out += ["", "Planning/evidence references: " + ', '.join(f"[{x}]({x})" for x in t['evidence']) + '.']
        out += [""]
    (ROOT / "TASKS.md").write_text('\n'.join(out)+'\n')
    out = ["# Paper B draft coverage", "", "Pinned active source: v1.1 draft, not published. The preserved public base is v1.0, DOI 10.5281/zenodo.24142496. These are proof obligations, not formal-verification claims. REUSE_CANDIDATE identifies relevant earlier code, not whole-statement certification.", "", "| Item | Statement | Formal status | Work packages | Claim facets |", "|---|---|---|---|---|"]
    for e in coverage['entries']:
        link = f"[source line {e['source_line']}](sources/paper-b-v1.1-draft.md#L{e['source_line']})"
        out += [f"| {e['id']} | {cell(e['title'])} ({link}) | {e['formal_status']} | {', '.join(e['tasks']) or 'open research'} | {cell(', '.join(e['claim_facets'])) or 'open question'} |"]
    out += ["", "E.1 and E.2 are representation examples assigned to PB5.4, outside the 32 numbered statements. Their finite instances do not establish a universal Boolean decision lower bound.", "", "## Root obligations", "", "These twelve architecture-level rows are the first-root burn-down. Exact Lean types are not yet frozen.", "", "| Obligation | Paper root | Owner | Status | Consumer |", "|---|---|---|---|---|"]
    for o in obligations['obligations']:
        out += [f"| {o['id']} — {cell(o['obligation'])} | {o['paper_root']} | {o['owner_role']} | {o['status']} | {cell(o['immediate_consumer'])} |"]
    out += ["", "## Structural extension obligations", "", "These later obligations do not enlarge the first threshold release cone.", "", "| Obligation | Paper item | Tasks | Status |", "|---|---|---|---|"]
    for o in obligations.get("extension_obligations", []):
        out += [f"| {o['id']} — {cell(o['obligation'])} | {o['paper_root']} | {', '.join(o['tasks'])} | {o['status']} |"]
    (ROOT / "COVERAGE.md").write_text('\n'.join(out)+'\n')
    out = ["# Paper B planning dashboard", "", "Snapshot generated from the editable JSON ledgers. This dashboard tracks work and proof scope; it is not a build or mathematical certificate.", "", f"- Active draft inventory: {s['paper_items']} items, including {s['proof_bearing_items']} proof-bearing statements and Question 6.2.", f"- Work inventory: {s['tasks']} packages in {s['milestones']} milestones.", f"- Completed planning audits: {s['task_status_counts'].get('DONE_PLAN',0)}.", f"- Newly certified Paper B roots: **{s['certified_new_roots']}**.", f"- Assigned workers: {s['assigned_workers']}; execution: {s['execution_status']}.", "- First delivery: Theorem 3.2 with every-query correctness, actual time, and peak working words.", "- Follow-on: Proposition 3.3 exact sharing, without claiming universal near-linear Λ.", "", "## Next dependency-ready work", ""]
    out += [f"- {t['id']}: {t['title']}." for t in task_ready(data)]
    out += ["", "The all-query/width/weighted revision scope is authorized. The next step is the revised architecture review, supported environment and exact typed-contract pilot. No theorem proof has started. Later optional branches do not block the first core release.", "", "See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).", ""]
    (ROOT / "DASHBOARD.md").write_text('\n'.join(out)+'\n')


def validate_links():
    for name in ["README.md", "PLAN.md", "MILESTONES.md", "TASKS.md", "COVERAGE.md", "DASHBOARD.md", "INTERFACES.md", "REUSE.md", "EXTERNAL-INPUTS.md", "DISPATCH.md", "contracts/release-contract.md"]:
        file = ROOT / name
        need(file.is_file(), f"missing plan document: {name}")
        for match in re.finditer(r"\]\(([^)]+)\)", file.read_text()):
            target = match.group(1).split('#')[0]
            if target and not re.match(r"[a-z]+://", target):
                need((file.parent / target).exists(), f"broken local link in {name}: {target}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["validate", "status", "ready", "show", "render"])
    parser.add_argument("task", nargs='?')
    args = parser.parse_args()
    try:
        data, coverage, obligations, external = load()
        index = validate_records(data, coverage, obligations, external)
        validate_files(data, coverage)
        if args.command == "render":
            render(data, coverage, obligations, external)
            validate_links()
            print("Rendered MILESTONES.md, TASKS.md, COVERAGE.md and DASHBOARD.md")
        elif args.command == "validate":
            validate_links()
            print(json.dumps({"result":"PASS", "scope":"plan/source/coverage integrity only; no Lean proof replay", **summary(data,coverage,obligations)}, indent=2))
        elif args.command == "status":
            print(json.dumps(summary(data, coverage, obligations), indent=2))
        elif args.command == "ready":
            print('\n'.join(f"{t['id']}: {t['title']} (owner: {t['owner_role']})" for t in task_ready(data)))
        elif args.command == "show":
            need(args.task in index, "show requires a known task ID")
            print(json.dumps(index[args.task], indent=2))
    except (PlanError, KeyError, OSError, json.JSONDecodeError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())

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
from zipfile import ZipFile

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


def validate_statement_graph(entries):
    """Check mathematical dependencies separately from the worker schedule."""
    visiting, complete = set(), set()

    def visit(item):
        need(item not in visiting, f"paper dependency cycle at {item}")
        if item in complete:
            return
        visiting.add(item)
        for dep in entries[item]["depends_on_items"]:
            need(dep in entries and entries[dep]["kind"] != "Question", f"{item}: invalid paper prerequisite {dep}")
            visit(dep)
        visiting.remove(item)
        complete.add(item)

    declarations = []
    for item, entry in entries.items():
        if entry["kind"] == "Question":
            need(not entry["proposed_declaration"] and not entry["depends_on_items"], f"{item}: open question has a formal target")
        else:
            need(entry["proposed_declaration"], f"{item}: missing planned declaration")
            declarations.append(entry["proposed_declaration"])
        visit(item)
    need(len(declarations) == len(set(declarations)), "duplicate proposed paper declaration")


STATEMENT_EVIDENCE = ("fidelity", "build", "axioms", "dependencies", "independent_replay")


def validate_statement_receipt(entry, entries):
    receipt = entry.get("verification", {})
    need(receipt.get("declaration") == entry["proposed_declaration"], f"{entry['id']}: missing statement-level declaration")
    for key in STATEMENT_EVIDENCE:
        need(receipt.get(key), f"{entry['id']}: missing statement-level {key}")
    need(all(entries[dep]["formal_status"] == "CERTIFIED" for dep in entry["depends_on_items"]),
         f"{entry['id']}: paper premise not certified")


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
    validate_statement_graph(entries)
    for tid in ids:
        for dep in index[tid]["dependencies"]:
            need(dep in index, f"{tid}: unknown dependency {dep}")

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

    for t in tasks:
        tid = t["id"]
        need(t["milestone"] in mids, f"{tid}: unknown milestone")
        need(t["status"] in STATUSES, f"{tid}: unknown task status")
        need(t["acceptance"] and t["obligation"], f"{tid}: missing acceptance contract")
        need(t["owner_role"] == data["module_owners"].get(t["planned_owner_module"]), f"{tid}: module owner conflict")
        for consumer in t["paper_consumers"]:
            need(consumer in entries and tid in entries[consumer]["tasks"], f"{tid}: unknown paper consumer {consumer}")
            need(consumer != "6.2", f"{tid}: open question must not be a proof consumer")
        if t["status"] == "DONE_PLAN":
            need(t["milestone"] == "EX0" and t["proof_status"] == "PLANNING_ONLY", f"{tid}: DONE_PLAN is not proof acceptance")
            need(t["evidence"], f"{tid}: missing planning evidence")
        if t["status"] == "VERIFIED":
            v = t.get("verification", {})
            required = {"source_manifest", "build", "axioms", "fidelity", "dependencies"}
            need(required.issubset(v), f"{tid}: verification record required; a task label is not proof evidence")
            need(t["proof_status"] == "CERTIFIED", f"{tid}: verified proof status mismatch")
        if t["status"] in {"READY", "VERIFIED", "DONE_PLAN"}:
            need(all(index[d]["status"] in CLOSED for d in t["dependencies"]), f"{tid}: incomplete dependencies for {t['status']}")
    for e in entries.values():
        need(e["formal_status"] in {"OPEN_RESEARCH", "NOT_CERTIFIED", "CERTIFIED"}, f"{e['id']}: unknown formal status")
        if e["kind"] == "Question":
            need(e["id"] == "6.2" and not e["tasks"] and e["formal_status"] == "OPEN_RESEARCH", "open question incorrectly assigned or certified")
        else:
            need(e["tasks"] and e["formal_status"] != "OPEN_RESEARCH", f"{e['id']}: uncovered paper statement")
        for tid in e["tasks"]:
            need(tid in index and e["id"] in index[tid]["paper_consumers"], f"{e['id']}: invalid coverage task {tid}")
        if e["formal_status"] == "CERTIFIED":
            proof_tasks = [index[x] for x in e["tasks"] if index[x]["proof_status"] != "PLANNING_ONLY"]
            need(proof_tasks and all(t["status"] == "VERIFIED" for t in proof_tasks) and all(index[x]["status"] in CLOSED for x in e["tasks"]), f"{e['id']}: certification without verified tasks")
            validate_statement_receipt(e, entries)
    roots = set(data["selected_roots"])
    need(roots == {"1.1", "4.1"} and roots == {o["paper_root"] for o in obligations["obligations"]}, "incorrect selected roots")
    oids = [o["id"] for o in obligations["obligations"] + obligations.get("extension_obligations", [])]
    need(len(oids) == len(set(oids)), "duplicate root obligation")
    for record in obligations["obligations"] + obligations.get("extension_obligations", []):
        need(record["status"] in {"OPEN", "CLOSED"}, f"{record['id']}: unknown obligation status")
    for o in obligations["obligations"]:
        need(o["paper_root"] in roots, f"{o['id']}: unapproved selected root")
        need(o["tasks"] and all(x in index and o["paper_root"] in index[x]["paper_consumers"] for x in o["tasks"]), f"{o['id']}: unknown obligation task")
        if o["status"] == "CLOSED":
            need(o["exact_type"] and o["evidence"] and all(index[x]["status"] == "VERIFIED" for x in o["tasks"]), f"{o['id']}: unsupported obligation closure")
    for o in obligations.get("extension_obligations", []):
        need(o["paper_root"] in entries and entries[o["paper_root"]]["kind"] != "Question" and o["tasks"] and all(x in index and o["paper_root"] in index[x]["paper_consumers"] for x in o["tasks"]), f"{o['id']}: invalid extension obligation")
        if o["status"] == "CLOSED":
            need(o["exact_type"] and o["evidence"] and all(index[x]["status"] == "VERIFIED" for x in o["tasks"]), f"{o['id']}: unsupported extension closure")
    for root in roots:
        if entries[root]["formal_status"] == "CERTIFIED":
            need(all(o["status"] == "CLOSED" for o in obligations["obligations"] if o["paper_root"] == root), f"{root}: open root obligation")
    for record in obligations.get("extension_obligations", []):
        if entries[record["paper_root"]]["formal_status"] == "CERTIFIED":
            need(record["status"] == "CLOSED", f"{record['paper_root']}: downstream obligation open")
    for x in external["inputs"]:
        need(x["consumers"] and all(tid in index for tid in x["consumers"]), f"{x['id']}: unknown external-input consumer")
    need(data["formal_roots_accepted"] == sum(entries[root]["formal_status"] == "CERTIFIED" for root in roots), "certified root count does not match coverage")
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
    first = {p for p, m in modules.items() if m["admission"] == "ORACLE_CORE"}
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
    structural = graph["structural_root"]
    need(structural in first, "missing structural proof module")
    ancestors = set()

    def structural_imports(path):
        if path in ancestors:
            return
        ancestors.add(path)
        for dep in modules[path]["local_imports"]:
            structural_imports(dep)

    structural_imports(structural)
    executable = {"Machine.lean", "Jumps.lean", "DomBuild.lean", "TreeIndex.lean",
                  "ForestBuild.lean", "Index.lean", "Resources.lean", "Oracle.lean"}
    need(not any(Path(path).name in executable for path in ancestors), "structural proof imports executable infrastructure")
    return {"planned_first_release_modules":len(first), "planned_unreachable_modules":len(first-reachable), "actual_proof_modules_created":sum((ROOT/p).exists() for p in modules)}


def statement_proof(source, match):
    """Bind separately located proofs to their statements, including the headline theorem."""
    item = match.group(2)
    first = source.find("\n\n", match.end())
    need(first != -1, f"{item}: incomplete statement")
    statement = source[match.start():first]
    if match.group(1) == "Question":
        return statement, "", None
    if item == "1.1":
        marker = "*Proof of Theorem 1.1.*"
        need(source.count(marker) == 1, "missing or ambiguous deferred proof of Theorem 1.1")
        start = source.index(marker, first)
    else:
        start = first + 2
        need(source.startswith("*Proof.*", start), f"{item}: expected a local proof")
    end = source.find("∎", start)
    need(end >= start and not PATTERN.search(source, start, end), f"{item}: incomplete proof")
    return statement, source[start:end+1], source.count("\n", 0, start) + 1


def validate_deposit(manuscript, coverage, lock):
    """Match the formalization source and figure to the published archive preserved locally."""
    release = lock["release"]
    receipt = read_json(PROJECT / release["receipt"])
    checks = read_json(PROJECT / release["release_check"])
    doi = receipt["zenodo"]["version_doi"]
    need(receipt["zenodo"]["status"] == "published" and lock["publication_status"] == coverage["publication_status"] == "PUBLISHED", "published edition required")
    need(manuscript["revision"] == receipt["version"] and receipt["artifact_commit"] == release["artifact_commit"], "publication receipt version mismatch")
    need(doi == lock["version_doi"] == manuscript["version_doi"] == coverage["version_doi"], "published version DOI mismatch")
    with ZipFile(PROJECT / release["source_archive"]) as archive:
        for key in (lock["active_canonical_path"], release["figure"]):
            file = PROJECT / key
            payload = archive.read(file.name)
            need(payload == file.read_bytes() and digest(payload) == checks["source_sha256"][file.name], f"deposit member mismatch: {file.name}")
    for key in ("pdf", "source_archive"):
        file = PROJECT / release[key]
        need(digest(file.read_bytes()) == checks["deposit_files"][file.name], f"release digest mismatch: {file.name}")


def validate_files(data, coverage):
    validate_module_graph(data, read_json(ROOT / "module-graph.json"))
    lock = read_json(ROOT / "sources/source-lock.json")
    for item in lock.get("canonical_files", []):
        file = PROJECT / item["path"]
        need(file.is_file() and digest(file.read_bytes()) == item["sha256"], f"canonical source mismatch: {item['path']}")
    need(data["manuscript"]["sha256"] == lock["active_sha256"], "tracker active-source identity mismatch")
    need(data["manuscript"]["revision"] == lock["paper_version"] and data["manuscript"]["canonical_path"] == lock["active_canonical_path"] and data["manuscript"]["status"] == lock["publication_status"] and coverage["paper_version"] == lock["paper_version"], "tracker active-source version/status mismatch")
    validate_deposit(data["manuscript"], coverage, lock)
    source = (ROOT / lock["active_source_path"]).read_text()
    need(digest(source.encode()) == lock["active_sha256"], "active source identity mismatch")
    need(digest(source.encode()) == coverage["paper_sha256"], "coverage paper identity mismatch")
    canonical = PROJECT / lock["active_canonical_path"]
    need(canonical.read_bytes() == source.encode(), "canonical manuscript differs from pinned source")
    matches = list(PATTERN.finditer(source))
    need([m.group(2) for m in matches] == [e["id"] for e in coverage["entries"]], "paper statement order or inventory mismatch")
    for m, e in zip(matches, coverage["entries"]):
        item = e["id"]
        statement, proof, line = statement_proof(source, m)
        need((e["kind"], e["title"]) == (m.group(1), m.group(3)), f"{item}: heading mismatch")
        need(source.count(f'<a id="statement-{item.replace(".", "-")}"></a>') == 1, f"{item}: broken stable anchor")
        need(statement == e["statement"] and digest(statement.encode()) == e["statement_sha256"], f"{item}: statement mismatch")
        need(e["source_line"] == source.count("\n", 0, m.start()) + 1, f"{item}: source line mismatch")
        need(line == e["proof_source_line"] and (digest(proof.encode()) if proof else None) == e["proof_sha256"], f"{item}: proof binding mismatch")
        combined = statement + ("\n\n" + proof if proof else "")
        need(digest(combined.encode()) == e["statement_and_proof_sha256"], f"{item}: statement/proof hash mismatch")
    for entry in coverage["entries"]:
        if entry["formal_status"] == "CERTIFIED":
            for key in STATEMENT_EVIDENCE:
                need((ROOT / entry["verification"][key]).is_file(), f"{entry['id']}: missing statement file {key}")
    for t in data["tasks"]:
        for path in t["evidence"]:
            need((ROOT / path).is_file(), f"{t['id']}: missing evidence file {path}")
        if t["status"] == "VERIFIED":
            for key, path in t["verification"].items():
                need((ROOT / path).is_file(), f"{t['id']}: missing verification artifact {key}")
    for o in read_json(ROOT / "obligations.json")["obligations"] + read_json(ROOT / "obligations.json").get("extension_obligations", []):
        if o["status"] == "CLOSED":
            need(all((ROOT / item).is_file() for item in o["evidence"]), f"{o['id']}: missing closure evidence")
    # This checks only ledger integrity. It does not execute a Lean checker or authenticate a future proof report.


def task_ready(data):
    index = {t["id"]: t for t in data["tasks"]}
    return [t for t in data["tasks"] if t["status"] in {"PLANNED", "READY"} and all(index[d]["status"] in CLOSED for d in t["dependencies"])]


def summary(data, coverage, obligations):
    manuscript = data["manuscript"]
    return {
        "source": f"Published Paper B {manuscript['revision']} (DOI {manuscript['version_doi']})",
        "milestones": len(data["milestones"]),
        "tasks": len(data["tasks"]),
        "task_status_counts": dict(sorted(Counter(t["status"] for t in data["tasks"]).items())),
        "paper_items": len(coverage["entries"]),
        "proof_bearing_items": sum(e["kind"] != "Question" for e in coverage["entries"]),
        "open_questions": [e["id"] for e in coverage["entries"] if e["kind"] == "Question"],
        "certified_new_roots": data["formal_roots_accepted"],
        "certified_paper_statements": sum(e["formal_status"] == "CERTIFIED" for e in coverage["entries"]),
        "paper_status": {e["id"]: e["formal_status"] for e in coverage["entries"]},
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
    out = ["# Paper B formalization milestones", "", "The work packages come from tasks.json. Use their dependencies to schedule parallel work. The counts distinguish planning from proof acceptance.", ""]
    for m in data["milestones"]:
        ts = [t for t in data["tasks"] if t["milestone"] == m["id"]]
        out += [f"## {m['id']} — {m['title']}", "", m["exit_gate"], "", f"Work packages: {len(ts)}; planning audits complete: {sum(t['status']=='DONE_PLAN' for t in ts)}; verified proof packages: {sum(t['status']=='VERIFIED' for t in ts)}.", "", "| Task | Owner | Status | Prerequisites |", "|---|---|---|---|"]
        out += [f"| [{t['id']}](TASKS.md#{t['id'].lower().replace('.', '')}) — {cell(t['title'])} | {t['owner_role']} | {t['status']} | {', '.join(t['dependencies']) or 'none'} |" for t in ts]
        out += [""]
    (ROOT / "MILESTONES.md").write_text('\n'.join(out)+'\n')
    out = ["# Paper B task tracker", "", "Each handoff has a proposed owner, prerequisites and acceptance evidence. Worker assignments and verified proof status are recorded separately.", ""]
    for t in data["tasks"]:
        out += [f'<a id="{t["id"].lower().replace(".", "")}"></a>', "", f"## {t['id']} — {t['title']}", "", f"- Milestone: {t['milestone']}; status: **{t['status']}**; proof status: {t['proof_status']}.", f"- Owner: {t['owner_role']}; reviewers: {', '.join(t['reviewer_roles']) or 'to assign'}; assigned worker: {t['assigned_agent'] or 'unassigned'}.", f"- Dependencies: {', '.join(t['dependencies']) or 'none'}.", f"- Proposed owner module: `{t['planned_owner_module']}`.", f"- Paper consumers: {', '.join(t['paper_consumers'])}; risk: {t['risk']}.", "", t['obligation'], "", "Acceptance:", ""]
        out += [f"- {a}" for a in t["acceptance"]]
        if t.get("progress"):
            out += ["", t["progress"]]
        if t['evidence']:
            out += ["", "Planning/evidence references: " + ', '.join(f"[{x}]({x})" for x in t['evidence']) + '.']
        out += [""]
    (ROOT / "TASKS.md").write_text('\n'.join(out)+'\n')
    out = ["# Published Paper B statement map", "", "Each row binds a paper statement to its proposed Lean declaration, immediate paper inputs and work packages. Independent acceptance uses the elaborated type and replay evidence.", "", "| Item | Statement | Proposed declaration | Paper inputs | Formal status | Work packages |", "|---|---|---|---|---|---|"]
    for e in coverage['entries']:
        anchor = e["id"].replace(".", "-")
        link = f"[statement](../{data['manuscript']['canonical_path']}#statement-{anchor})"
        out += [f"| {e['id']} | {cell(e['title'])} ({link}) | {e['proposed_declaration'] or '—'} | {', '.join(e['depends_on_items']) or '—'} | {e['formal_status']} | {', '.join(e['tasks']) or '—'} |"]
    out += ["", "Theorem 1.1 is proved in Section 5. The ledger records a separate hash for its deferred proof. Question 6.2 concerns three or more failures.", "", "## Root obligations", "", "The first two formal targets are the oracle theorem and its exit-set transfer identity. These obligations specify what each formal statement must capture.", "", "| Obligation | Paper root | Owner | Status | Consumer |", "|---|---|---|---|---|"]
    for o in obligations['obligations']:
        out += [f"| {o['id']} — {cell(o['obligation'])} | {o['paper_root']} | {o['owner_role']} | {o['status']} | {cell(o['immediate_consumer'])} |"]
    out += ["", "## Structural extension obligations", "", "The listed batch and the guarded-output application depend on the oracle.", "", "| Obligation | Paper item | Tasks | Status |", "|---|---|---|---|"]
    for o in obligations.get("extension_obligations", []):
        out += [f"| {o['id']} — {cell(o['obligation'])} | {o['paper_root']} | {', '.join(o['tasks'])} | {o['status']} |"]
    (ROOT / "COVERAGE.md").write_text('\n'.join(out)+'\n')
    out = ["# Paper B planning dashboard", "", "Snapshot generated from the editable JSON ledgers. This dashboard tracks work and proof scope; it is not a build or mathematical certificate.", "", f"- Published edition inventory: {s['paper_items']} items, including {s['proof_bearing_items']} proof-bearing statements and Question 6.2.", f"- Work inventory: {s['tasks']} packages in {s['milestones']} milestones.", f"- Completed planning audits: {s['task_status_counts'].get('DONE_PLAN',0)}.", f"- Certified main theorems: **{s['certified_new_roots']}/2**. Certified numbered results: **{s['certified_paper_statements']}/{s['proof_bearing_items']}**.", f"- Assigned workers: {s['assigned_workers']}; execution: {s['execution_status']}.", "- Oracle milestone: Theorem 1.1, with one index built before the failures and target are named, including preprocessing, peak and retained words, query correctness and cost.", "- First main proof milestone: Theorem 4.1, equality of both exit-tail sets under nested cuts before any LCA compression."]
    counts = s["task_status_counts"]
    verified = counts.get("VERIFIED", 0)
    planning = counts.get("DONE_PLAN", 0)
    milestone_counts = Counter(m["status"] for m in data["milestones"])
    out += [
        "", "## Completed and remaining", "",
        f"- Completed work packages **{verified + planning}/{s['tasks']}**. "
        f"Planning audits **{planning}** and verified proof packages **{verified}**.",
        f"- Remaining work packages **{s['tasks'] - verified - planning}**. "
        + ", ".join(f"{n} {state.lower().replace('_', ' ')}"
                    for state, n in counts.items() if state not in CLOSED) + ".",
        "- Milestones " + ", ".join(f"{n} {state.lower().replace('_', ' ')}"
                                   for state, n in sorted(milestone_counts.items())) + ".",
        "- [EX2.2 unattended batch](unattended/README.md) has its own declaration-by-declaration status.",
    ]
    ongoing = [t for t in data["tasks"] if t["status"] == "IN_PROGRESS"]
    if ongoing:
        out += ["", "## In progress", ""]
        for t in ongoing:
            anchor = t["id"].lower().replace(".", "")
            out.append(f"- [{t['id']}](TASKS.md#{anchor}) — {t['progress'] if t.get('progress') else t['title']}")
    ready = task_ready(data)
    if ready:
        out += ["", "## Ready to start", ""]
        out += [f"- {t['id']} — {t['title']}." for t in ready]
    out += ["", "See the [theorem chain](PLAN.md) and the [reusable Lean declarations](REUSE.md).", "", "See [milestones](MILESTONES.md), [tasks](TASKS.md), [coverage](COVERAGE.md), [interfaces](INTERFACES.md), and the [proposed contract](contracts/release-contract.md).", ""]
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

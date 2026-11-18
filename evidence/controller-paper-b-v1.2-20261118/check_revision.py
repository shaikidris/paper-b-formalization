#!/usr/bin/env python3
"""Check the v1.2 edition, preserved companion proofs, and formalization inventory."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
TRACKER = PROJECT / "paper-b-formalization"
EVIDENCE = PROJECT / "evidence/paper-b-space-20261118"
sys.path.insert(0, str(TRACKER))
import plan


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def check_local_links(path):
    for target in re.findall(r"\[[^\]\n]*\]\(([^)\n]+)\)", path.read_text()):
        if re.match(r"[a-z]+:", target):
            continue
        fragment_path, _, fragment = target.partition("#")
        linked = (path.parent / fragment_path) if fragment_path else path
        require(linked.is_file(), f"{path.name}: missing {target}")
        if fragment.startswith("statement-"):
            require(f'id="{fragment}"' in linked.read_text(), f"{path.name}: missing anchor {target}")


def companion_blocks(text):
    blocks = {}
    for match in plan.PATTERN.finditer(text):
        number = match.group(2)
        if number not in {"3.1", "3.2", "3.3"}:
            continue
        end = text.index("∎", match.end())
        require(number not in blocks and not plan.PATTERN.search(text, match.end(), end),
                f"Incomplete or duplicate companion item {number}")
        blocks[number] = text[match.start():end+1]
    return blocks


def check_manuscripts(article, companion, older):
    main, previous, supplement = (p.read_text() for p in (article, older, companion))
    require(sha(older) == "957acfa0914524ab7e6501d90b3da09cf9babf1901b3cdddac09d52f6205fada", "v1.1 source mismatch")
    require(sha(article) == "f62cda3d37658f5158bda908c03518fae5f04f59fa1a68b14cb4f312878d4d0c", "v1.2 edition mismatch")
    originals = companion_blocks(previous)
    require(set(originals) == {"3.1", "3.2", "3.3"} and companion_blocks(supplement) == originals,
            "A threshold theorem or proof differs from its v1.1 text")
    for path in (article, companion):
        check_local_links(path)
    statement_ids = {m.group(2) for m in plan.PATTERN.finditer(main)}
    body, refs = main.split("## References\n")
    prose = re.sub(r"\[[^]\n]*\]", "", body)
    for number in re.findall(r"\b(?:Theorem|Lemma|Corollary|Question) (\d+\.\d+)", prose):
        require(number in statement_ids, f"Unknown internal result {number}")
    for key in re.findall(r"^- \[([^]]+)\]", refs, re.M):
        require(re.search(r"\b" + re.escape(key) + r"\b", body), f"Uncited entry {key}")
    for marker in ("**Funding.**", "**Competing interests.**", "**AI assistance.**"):
        line = next(s for s in previous.splitlines() if s.startswith(marker))
        require(line in main.splitlines(), f"Recheck declaration {marker}")
    abstract = main.partition("## Abstract\n")[2].partition("\n## 1.")[0].strip()
    require("\n\n" not in abstract and "exit-transfer theorem" in abstract, "Abstract or theorem lead mismatch")
    require("threshold tradeoff for all-query batches" not in main, "Offline proof duplicated in main article")
    return {"main_words": len(main.split()), "previous_words": len(previous.split()), "companion_words": len(supplement.split()),
            "abstract_words": len(abstract.split()), "abstract_characters": len(abstract),
            "threshold_blocks_byte_identical": sorted(originals), "main_sha256": sha(article), "companion_sha256": sha(companion)}


def check_manifest():
    manifest = read_json(TRACKER / "artifact-manifest.json")
    found = {str(file.relative_to(TRACKER)):file for file in TRACKER.rglob("*")
             if file.is_file() and file.name not in {".DS_Store", "artifact-manifest.json"}
             and not {".git", ".lake", "__pycache__"}.intersection(file.relative_to(TRACKER).parts)}
    expected = {row["path"]:row for row in manifest["files"]}
    require(len(expected) == len(manifest["files"]) and set(found) == set(expected), "Tracker manifest inventory mismatch")
    for name, path in found.items():
        row = expected[name]
        require(row["bytes"] == path.stat().st_size and row["sha256"] == sha(path), f"Tracker manifest mismatch for {name}")
    return len(found)


def run_finite_checks():
    for script, record in (("check_exit_transfer_review.py","exit-transfer-review-checks.json"),
                           ("check_dag_exit.py","dag-exit-checks.json")):
        output = subprocess.check_output([sys.executable, "-B", str(EVIDENCE / script)], cwd=EVIDENCE, text=True)
        require(json.loads(output) == read_json(EVIDENCE / record), f"Finite checker differs from {record}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--replay", action="store_true", help="Also rerun both archived exhaustive checkers")
    args = parser.parse_args()
    data, coverage, obligations, external = plan.load()
    plan.validate_records(data, coverage, obligations, external)
    plan.validate_files(data, coverage)
    plan.validate_links()
    # Replay the specific pre-publication edition audited by this historical check.
    article = PROJECT / "papers/controller/paper-b-two-failure-reachability-v1.2-draft.md"
    companion = article.with_name("paper-b-threshold-companion-v1.2.md")
    older = article.with_name("paper-b-guarded-reachability-v1.1-draft.md")
    report = check_manuscripts(article, companion, older)
    report["tracker_files_verified"] = check_manifest()
    report["items"] = [e["id"] for e in coverage["entries"]]
    report["selected_lean_roots"] = data["selected_roots"]
    report["certified_lean_roots"] = data["formal_roots_accepted"]
    counts = read_json(EVIDENCE / "exit-transfer-review-checks.json")
    for count in (counts["proof_identity"]["exact_first_arc_identities"], counts["proof_identity"]["flat_graphs"],
                  counts["proof_identity"]["both_terms_indispensable"], counts["oracle_all_sources"]["graphs"],
                  counts["oracle_all_sources"]["singleton_answers"]):
        require(format(count, ",") in article.read_text(), f"Manuscript missing checked count {count}")
    if args.replay:
        run_finite_checks()
    report["finite_replay_this_run"] = args.replay
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

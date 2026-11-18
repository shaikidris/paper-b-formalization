"""Check the revised oracle against graph search and test append-only skew jumps."""
from pathlib import Path
import json
import random
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / "paper-b-space-20261118"


def check_jumps(tree_type):
    tree = tree_type()
    depth = 8192
    for v in range(depth):
        tree.add(v)
    rng = random.Random(20261118)
    pairs = [(v, w) for v in range(513) for w in range(v + 1)]
    pairs += [(v, rng.randrange(v + 1)) for v in range(513, depth + 1)]
    pairs += [(depth, w) for w in range(depth + 1)]
    highest = 0
    for node, level in pairs:
        steps = 0
        while node != level:
            jump = tree.jump[node]
            node = jump if jump >= level else tree.parent[node]
            steps += 1
            assert steps <= 3 * (depth + 1).bit_length()
        highest = max(highest, steps)
    for v in range(8193, 12000):
        tree.add(rng.randrange(v))
    for v in range(8193, 12000):
        slow = v
        for level in range(tree.depth[v], -1, -1):
            assert tree.at_depth(v, level) == slow
            slow = tree.parent[slow]
    return {"chain_depth": depth, "chain_queries": len(pairs), "max_moves": highest,
            "additional_branch_insertions": 12000 - 8193}


def main():
    with tempfile.TemporaryDirectory() as work:
        for p in BASE.glob("*.py"):
            shutil.copyfile(p, Path(work) / p.name)
        subprocess.run(["patch", "-s", "-p0", "-i", str(HERE / "oracle.patch")],
                       cwd=work, check=True)
        sys.path.insert(0, work)
        from antichain_time import GrowingTree
        from check_exit_transfer_review import test_all_sources, check_distinct_exit_tails
        from check_dag_exit import sample_lists, expanded_checks

        result = {
            "jumps": check_jumps(GrowingTree),
            "all_sources": test_all_sources(),
            "sample_lists": sample_lists(),
            "expanded": expanded_checks(),
            "distinct_tails": check_distinct_exit_tails(),
        }
        print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

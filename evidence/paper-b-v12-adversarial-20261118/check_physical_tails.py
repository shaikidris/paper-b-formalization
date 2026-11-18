"""Independent physical-tail and last-exit tests. Standard library only."""
from collections import Counter
from itertools import combinations, product
import json


def reachable(graph, source, failed):
    if source in failed:
        return set()
    seen = {source}
    stack = [source]
    while stack:
        for child in graph[stack.pop()]:
            if child not in failed and child not in seen:
                seen.add(child)
                stack.append(child)
    return seen


def skeletons(n):
    # List all rooted flat ordered skeletons. A reachable flat prefix
    # gives a new vertex no nonroot dominator iff it has a root arc
    # or at least two distinct predecessors.
    choices = []
    for v in range(1, n):
        choices.append([tuple(u for u in range(v) if mask & (1 << u))
                        for mask in range(1, 1 << v) if mask & 1 or mask.bit_count() >= 2])
    for predecessors in product(*choices):
        graph = [[] for _ in range(n)]
        for v, parents in enumerate(predecessors, 1):
            for u in parents:
                graph[u].append(v)
        yield graph


def cut_forest_edges(graph):
    n = len(graph)
    vertices = set(range(n))
    proper = {}
    for pair in combinations(range(1, n), 2):
        cut = frozenset(pair)
        loss = vertices - cut - reachable(graph, 0, cut)
        if loss:
            proper[cut] = loss
    adjacent = []
    for child, loss in proper.items():
        supersets = [cut for cut, other in proper.items() if loss < other]
        if supersets:
            parent = min(supersets, key=lambda cut: len(proper[cut]))
            assert all(proper[parent] <= proper[cut] for cut in supersets)
            adjacent.append((parent, child))
    return proper, adjacent


def realize(graph, variant):
    # Two private leaves of each nonroot block are physically distinct
    # tails. Several tails may feed the same quotient head, and the same
    # tail may feed different heads. Repeated arcs do not create new tails.
    n = len(graph)
    physical = [[] for _ in range(n + 2 * (n - 1))]
    options = {u:(u, n+2*(u-1), n+2*(u-1)+1) for u in range(1, n)}
    labelled = {}
    for u, heads in enumerate(graph):
        if u == 0:
            physical[0].extend(heads)
            continue
        physical[u].extend(options[u][1:])
        for w in heads:
            mask = 1 + (3*u + 5*w + variant*(w+1)) % 7
            tails = tuple(x for j, x in enumerate(options[u]) if mask >> j & 1)
            labelled[u,w] = tails
            for x in tails:
                physical[x].append(w)
            physical[tails[0]].append(w)
    return physical, options, labelled


def evaluate(graph, losses, adjacent, variant, counts):
    physical, options, labels = realize(graph, variant)
    n = len(graph)
    all_physical = set(range(len(physical)))
    single = {a:reachable(physical, 0, {a}) for a in all_physical}
    for u, members in options.items():
        assert all_physical - single[u] == set(members)
        assert all_physical - single[members[1]] == {members[1]}
        assert all_physical - single[members[2]] == {members[2]}
    reach_suffix = {}
    def exits(cut, u, y):
        tails = set()
        for w in graph[u]:
            key = cut, w
            if key not in reach_suffix:
                reach_suffix[key] = reachable(graph, w, cut)
            if y in reach_suffix[key]:
                tails.update(labels[u,w])
        return tails

    for outer, child in adjacent:
        fresh = child - outer
        counts["adjacent_real_pairs"] += 1
        counts["disjoint_pairs" if not outer & child else "shared_pairs"] += 1
        assert fresh <= losses[outer]
        assert all(p > max(outer) for p in fresh)
        u,v = sorted(outer)
        for y in losses[child]:
            sigmas = {}
            for endpoint in (u, v):
                observed = exits(outer, endpoint, y)
                base = set().union(*(exits(outer, endpoint, p) for p in fresh))
                inherited = exits(child, endpoint, y) if endpoint in child else set()
                assert observed and observed == base | inherited, (graph, variant, outer, child, y, endpoint)
                counts["physical_tail_set_equalities"] += 1
                counts["omitting_fresh_changes_set"] += bool(observed - inherited)
                counts["omitting_inherited_changes_set"] += bool(observed - base)
                counts["both_needed_same_coordinate"] += bool(base-inherited and inherited-base)
                # Physically each block is a star, so its literal LCA is
                # either the unique member or the block root.
                sigmas[endpoint] = next(iter(observed)) if len(observed)==1 else endpoint
            for a,b in product(options[u], options[v]):
                by_lca = sigmas[u] in single[a] or sigmas[v] in single[b]
                by_dfs = y in reachable(physical, 0, {a,b})
                assert by_lca == by_dfs, (graph, variant, outer, child, y, a, b)
                counts["two_failure_physical_dfs_comparisons"] += 1
                # Replacing every physical exit tail by its quotient root.
                counts["root_only_shortcut_disagrees"] += (u in single[a] or v in single[b]) != by_dfs


def main():
    counts = Counter()
    for n in range(1, 7):
        for graph in skeletons(n):
            counts["ordered_flat_skeletons"] += 1
            losses, adjacent = cut_forest_edges(graph)
            if adjacent:
                counts["skeletons_with_nested_cuts"] += 1
                for variant in range(2):
                    counts["tested_physical_realizations"] += 1
                    evaluate(graph, losses, adjacent, variant, counts)
    assert all(counts[k] for k in ("disjoint_pairs", "shared_pairs", "both_needed_same_coordinate",
                                   "root_only_shortcut_disagrees"))
    print(json.dumps(dict(sorted(counts.items())), indent=2))


if __name__ == "__main__":
    main()

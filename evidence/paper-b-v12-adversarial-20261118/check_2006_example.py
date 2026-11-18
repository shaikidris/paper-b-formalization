"""Evaluate IADIS 2006 Definition 1 on the two-branch example."""
from itertools import combinations


def common_pairs(terminals, paths, vertices):
    relevant = [set(path) for z in terminals for path in paths[z]]
    answer = set()
    for pair in combinations(sorted(vertices - set(terminals)), 2):
        a, b = pair
        if (all(p.intersection(pair) for p in relevant)
                and any(a in p and b not in p for p in relevant)
                and any(b in p and a not in p for p in relevant)):
            answer.add(pair)
    return answer


if __name__ == "__main__":
    paths = {"u1":[("u1","a","c","r")], "u2":[("u2","b","d","r")]}
    vertices = set().union(*(p[0] for p in paths.values()))
    assert common_pairs(["u1"], paths, vertices) == set()
    assert common_pairs(["u2"], paths, vertices) == set()
    result = common_pairs(["u1","u2"], paths, vertices)
    assert result == {("a","b"), ("a","d"), ("b","c"), ("c","d")}
    print("Both singleton chains empty. Joint proper pairs:", sorted(result))

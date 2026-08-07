#!/usr/bin/env python3
"""Exhaustive small-grid checks for LAMINAR_MULTI_EXCHANGE.md."""

from __future__ import annotations

from itertools import combinations


OUT = (-1, -1)


def grid_dual(n: int):
    edges = []
    for r in range(n):
        for c in range(n - 1):
            primal = ((r, c), (r, c + 1))
            above = (r - 1, c) if r else OUT
            below = (r, c) if r < n - 1 else OUT
            edges.append((above, below, primal))
    for r in range(n - 1):
        for c in range(n):
            primal = ((r, c), (r + 1, c))
            left = (r, c - 1) if c else OUT
            right = (r, c) if c < n - 1 else OUT
            edges.append((left, right, primal))
    vertices = [OUT] + [(r, c) for r in range(n - 1) for c in range(n - 1)]
    return vertices, edges


def is_tree(vertices, edges, chosen):
    parent = {v: v for v in vertices}

    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for i in chosen:
        a, b, _ = edges[i]
        a, b = root(a), root(b)
        if a == b:
            return False
        parent[a] = b
    return len(chosen) == len(vertices) - 1


def trees(n):
    vertices, edges = grid_dual(n)
    for chosen in combinations(range(len(edges)), len(vertices) - 1):
        if is_tree(vertices, edges, chosen):
            yield vertices, edges, frozenset(chosen)


def degrees(edges, chosen):
    ans = {}
    for i in chosen:
        for v in edges[i][2]:
            ans[v] = ans.get(v, 0) + 1
    return ans


def waste(edges, chosen):
    return sum(3 - d for d in degrees(edges, chosen).values())


def component_without(vertices, edges, chosen, removed, start):
    adjacency = {v: [] for v in vertices}
    for i in chosen - {removed}:
        a, b, _ = edges[i]
        adjacency[a].append(b)
        adjacency[b].append(a)
    seen = {start}
    stack = [start]
    while stack:
        for v in adjacency[stack.pop()]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return seen


def crossing(edges, shore):
    return {
        i for i, (a, b, _) in enumerate(edges) if (a in shore) != (b in shore)
    }


def check_n3_exchange_formula():
    all_trees = list(trees(3))
    _, edges, _ = all_trees[0]
    for _, _, first in all_trees:
        d_first = degrees(edges, first)
        support_first = set(d_first)
        for _, _, second in all_trees:
            support_second = set(degrees(edges, second))
            new = support_second - support_first
            lost = support_first - support_second
            assert waste(edges, second) - waste(edges, first) == 3 * (
                len(new) - len(lost)
            )
    return len(all_trees)


def find_reused_protector():
    """Find one unsupported vertex protecting swaps at distinct private vertices."""
    for n in (3, 4):
        candidates = []
        minimum = None
        for vertices, edges, chosen in trees(n):
            value = waste(edges, chosen)
            if minimum is None or value < minimum:
                minimum, candidates = value, [(vertices, edges, chosen)]
            elif value == minimum:
                candidates.append((vertices, edges, chosen))
        for vertices, edges, chosen in candidates:
            d = degrees(edges, chosen)
            uses = {}
            for f in chosen:
                a, _, primal_f = edges[f]
                shore = component_without(vertices, edges, chosen, f, a)
                for x in primal_f:
                    if d[x] != 1:
                        continue
                    for e in crossing(edges, shore) - chosen:
                        if x in edges[e][2]:
                            continue
                        for z in edges[e][2]:
                            if d.get(z, 0) == 0:
                                uses.setdefault(z, set()).add((x, f, e))
            for z, triples in uses.items():
                xs = {x for x, _, _ in triples}
                fs = {f for _, f, _ in triples}
                if len(xs) >= 2 and len(fs) >= 2:
                    return n, minimum, edges, chosen, z, sorted(triples)
    raise AssertionError("no reused protector found through n=4")


def find_no_common_protector_and_bad_simultaneous_exchange():
    for n in (3, 4):
        all_trees = list(trees(n))
        minimum = min(waste(edges, chosen) for _, edges, chosen in all_trees)
        minimum_trees = [
            item for item in all_trees if waste(item[1], item[2]) == minimum
        ]
        no_common = None
        for vertices, edges, chosen in minimum_trees:
            d = degrees(edges, chosen)
            cuts = {
                f: crossing(
                    edges,
                    component_without(vertices, edges, chosen, f, edges[f][0]),
                )
                for f in chosen
            }
            for f in chosen:
                _, _, primal_f = edges[f]
                for x in primal_f:
                    if d[x] != 1:
                        continue
                    eligible = [
                        e for e in cuts[f] - chosen if x not in edges[e][2]
                    ]
                    protectors = [
                        {z for z in edges[e][2] if d.get(z, 0) == 0}
                        for e in eligible
                    ]
                    if protectors and not set.intersection(*protectors):
                        no_common = (n, edges, chosen, x, f, eligible, protectors)
                        break
                if no_common:
                    break
            if no_common:
                break
        bad = None
        for vertices, edges, chosen in all_trees:
            cuts = {
                f: crossing(
                    edges,
                    component_without(vertices, edges, chosen, f, edges[f][0]),
                )
                for f in chosen
            }
            for f1, f2 in combinations(chosen, 2):
                for e1 in cuts[f1] - chosen:
                    for e2 in cuts[f2] - chosen:
                        if e1 == e2:
                            continue
                        replacement = chosen - {f1, f2} | {e1, e2}
                        if not is_tree(vertices, edges, replacement):
                            bad = (n, edges, chosen, f1, f2, e1, e2)
                            break
                    if bad:
                        break
                if bad:
                    break
            if bad:
                break
        if no_common and bad:
            return no_common, bad
    raise AssertionError("counterexamples not found through n=4")


def fmt_edge(edges, i):
    a, b, primal = edges[i]
    return f"{i}:dual={a}-{b},primal={primal}"


def main():
    count = check_n3_exchange_formula()
    n, minimum, edges, chosen, z, triples = find_reused_protector()
    print(f"n=3 trees checked pairwise: {count}")
    print(f"reused protector: n={n}, minimum W={minimum}, z={z}")
    print("tree:")
    for i in sorted(chosen):
        print(" ", fmt_edge(edges, i))
    print("protected swaps (private vertex, removed edge, added edge):")
    for x, f, e in triples:
        print(" ", x, fmt_edge(edges, f), "=>", fmt_edge(edges, e))
    no_common, bad = find_no_common_protector_and_bad_simultaneous_exchange()
    n, edges, chosen, x, f, eligible, protectors = no_common
    print(f"no common protector: n={n}, private x={x}, removed={fmt_edge(edges, f)}")
    print("tree:")
    for i in sorted(chosen):
        print(" ", fmt_edge(edges, i))
    for e, ps in zip(eligible, protectors):
        print(" ", fmt_edge(edges, e), "protectors=", sorted(ps))
    n, edges, chosen, f1, f2, e1, e2 = bad
    print(f"bad simultaneous choices: n={n}")
    print("tree:")
    for i in sorted(chosen):
        print(" ", fmt_edge(edges, i))
    print(" removed", fmt_edge(edges, f1), "and", fmt_edge(edges, f2))
    print(" added  ", fmt_edge(edges, e1), "and", fmt_edge(edges, e2))


if __name__ == "__main__":
    main()

"""Endpoint/frame and budgeted notch experiments at sides 11 and 14 only.

Importing runs no search. All partitions include ambient isolates.
"""

from analysis.searches import l2_rail_repair_research as repair


def endpoint_window(s):
    """Free both right endpoints, the intervening frame, and the bottom pocket."""
    if s not in (2, 3):
        raise ValueError("only s=2,3 (n=11,14) are permitted")
    n, source = repair.staircase(s)
    h = 3 * s
    variable = {(r, c) for r in range(h - 3, h + 3)
                for c in range(h + 2, h + 5)}
    variable |= {(r, c) for r in (h + 1, h + 2)
                 for c in range(2, h + 3)}
    return n, source, source - variable, variable


def attachment_partition(n, centers, vertices):
    """Canonical actual blocks on named ports, not root labels or sizes."""
    parent = repair.forced_partition(n, centers)
    blocks = {}
    for v in sorted(set(vertices)):
        blocks.setdefault(repair.root(parent, v), []).append(v)
    return tuple(sorted(tuple(block) for block in blocks.values()))


def double_cut(s):
    n, source, _, _ = endpoint_window(s)
    h = 3 * s
    pocket = {(r, c) for r in (h + 1, h + 2) for c in range(2, h + 3)}
    fixed = source - pocket - {(h - 3, h + 2), (h, h + 2)}
    return n, fixed


def notch_window(s):
    n, source, _, variable = endpoint_window(s)
    h = 3 * s
    variable |= {(h, c) for c in range(s + 3, s + 6)}
    variable |= {(h - 1, s + 4), (h + 1, s + 4)}
    return n, source, source - variable, variable


def search_notch(s, mode, node_budget=100000):
    """Cardinality search with optional monotone rootless-output constraint.

    Exhaustive is true only if no subtree was stopped by the node budget.
    A budget-limited best is a feasible lower bound, never a reported maximum.
    """
    if mode not in ("unrestricted", "rootless", "joined-rootless"):
        raise ValueError("unknown output mode")
    if node_budget < 1:
        raise ValueError("node budget must be positive")
    n, source, fixed, variable = notch_window(s)
    h = 3 * s
    required = {(h - 1, s + 4), (h + 1, s + 4)} if mode == "joined-rootless" else set()
    fixed |= required
    initial = repair.forced_partition(n, fixed)
    boundary = [(r, c) for r in range(n) for c in range(n)
                if r in (0, n - 1) or c in (0, n - 1)]
    port = (h - 3, s + 2)

    def output_ok(parent):
        return mode == "unrestricted" or all(
            repair.root(parent, port) != repair.root(parent, b) for b in boundary)

    assert output_ok(initial)
    best = set(fixed)
    nodes = 0
    exhaustive = True

    def visit(centers, parent, choices):
        nonlocal best, nodes, exhaustive
        if nodes == node_budget:
            exhaustive = False
            return
        nodes += 1
        if len(centers) > len(best):
            best = centers.copy()
        if len(centers) + len(choices) <= len(best):
            return
        legal = []
        for v in choices:
            updated = repair.insert(n, centers, parent, v)
            if updated is not None and output_ok(updated):
                legal.append((v, updated))
        while legal and exhaustive:
            if len(centers) + len(legal) <= len(best):
                break
            v, updated = legal.pop(0)
            visit(centers | {v}, updated, [w for w, _ in legal])

    visit(fixed, initial, sorted(variable - fixed))
    rebuilt = repair.forced_partition(n, best)
    assert output_ok(rebuilt)
    assert required <= best
    return {"centers": best, "nodes": nodes, "exhaustive": exhaustive,
            "profile": repair.profile(n, best)}


def notch_experiments():
    for s in (2, 3):
        n, source, _, variable = notch_window(s)
        h = 3 * s
        ports = [(h - 3, s + 2), (h, h + 1), (h + 3, h + 1),
                 (h - 1, s + 4), (h + 1, s + 4)]
        for mode in ("unrestricted", "rootless", "joined-rootless"):
            result = search_notch(s, mode)
            centers = result["centers"]
            if mode == "joined-rootless" and result["exhaustive"]:
                assert centers == joined_witness(s)[1]
            print(s, "notch", mode, "variables", len(variable),
                  "nodes", result["nodes"], "exhaustive", result["exhaustive"],
                  "profile", result["profile"],
                  "delete", sorted(source - centers),
                  "insert", sorted(centers - source),
                  "ports", attachment_partition(n, centers, ports), flush=True)
        n, centers = joined_witness(s)
        ports = [(h - 3, s + 2), (h + 1, s + 4), (h + 3, h + 1)]
        next_center = (h + 1, s + 5)
        attachments = [next_center] + [v for v in repair.neighbors(n, next_center)
                                       if v not in centers]
        print(s, "first-extension-blocked", next_center,
              attachment_partition(n, centers, attachments), flush=True)
        assert repair.insert(n, centers, repair.forced_partition(n, centers), next_center) is None
        cleared = centers - {(h, s + 6)}
        extended, signatures = repair.audit_insertions(n, cleared, [{next_center}])
        following = (h + 1, s + 6)
        parent = repair.forced_partition(n, extended)
        update = repair.insert(n, extended, parent, following)
        if update is not None:
            assert repair.root(update, ports[0]) == repair.root(update, ports[2])
        print(s, "paid-extension", repair.profile(n, extended), signatures,
              "ports", attachment_partition(n, extended, ports),
              "following", following, "legal", update is not None,
              "following-ports", attachment_partition(n, extended,
                  [following] + [v for v in repair.neighbors(n, following)
                                 if v not in extended]), flush=True)


def joined_witness(s):
    """First maximizing joined-rootless witnesses, not a uniform constructor."""
    n, source, _, _ = notch_window(s)
    h = 3 * s
    deleted = {(h - 3, h + 4)} | {(h, c) for c in range(s + 3, s + 6)}
    deleted |= {v for v in source if v[0] in (h + 1, h + 2) and
                2 <= v[1] <= h + 2}
    added = {(h - 1, s + 4)} | {(h + 1, c) for c in range(s + 2, s + 5)}
    if s == 3:
        added.add((h + 2, 3))
    return n, source - deleted | added


def main():
    for s in (2, 3):
        n, source, fixed, variable = endpoint_window(s)
        for mode in ("fixed-frame", "free-frame"):
            boundary = {v for v in variable if v[1] == n - 1}
            held = fixed | (source & boundary) if mode == "fixed-frame" else fixed
            choices = variable - boundary if mode == "fixed-frame" else variable
            best, nodes = repair.maximize(n, held, choices)
            result = held | best
            assert len(result) == {2: 48, 3: 76}[s]
            print(s, mode, "variables", len(choices), "nodes", nodes,
                  "profile", repair.profile(n, result),
                  "delete", sorted(source - result),
                  "insert", sorted(result - source), flush=True)
        n, cut = double_cut(s)
        h = 3 * s
        bridge = (h + 2, h + 1)
        result, signatures = repair.audit_insertions(n, cut, [{bridge}])
        print(s, "double-cut-bridge", repair.profile(n, result), signatures,
              "rail-ports", attachment_partition(n, result,
                  [(h - 3, h + 1), (h, h + 1), (h + 3, h + 1)]), flush=True)
        pocket = {v for v in source if v[0] in (h + 1, h + 2) and
                  2 <= v[1] <= h + 2}
        restored, _ = repair.audit_insertions(n, result, [{v} for v in sorted(pocket)])
        assert len(restored) == len(source) - 1
        print(s, "double-cut-with-pocket", repair.profile(n, restored), flush=True)
    notch_experiments()


if __name__ == "__main__":
    main()

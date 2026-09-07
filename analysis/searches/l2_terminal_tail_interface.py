"""Budgeted terminal-tail/last-left experiments, only n=11/14; inert on import."""

from analysis.searches import l2_rail_repair_research as repair
from analysis.searches import l2_two_rail_interface as two


def window(s, left=False):
    n, source, _, variable = two.notch_window(s)
    h = 3 * s
    variable |= {(h, c) for c in range(s + 6, h + 3)}
    if left:
        # Entire last left rail, its boundary spoke, and the lower join corridor.
        variable |= {(h - 1, c) for c in range(s + 2)}
        variable |= {(h, s + 1), (h + 1, s + 1)}
    return n, source, source - variable, variable


def required_centers(s, reach):
    if s not in (2, 3):
        raise ValueError("only s=2,3 (n=11,14) are permitted")
    h = 3 * s
    required = {(h - 1, s + 4), (h + 1, s + 4)}
    if reach == "right":
        required |= {(h + 1, c) for c in range(s + 2, h + 2)}
    elif reach == "left":
        required |= {(h + 1, c) for c in range(s + 1, s + 5)}
    elif reach == "both":
        required |= {(h + 1, c) for c in range(s + 1, h + 2)}
    elif reach != "joined":
        raise ValueError("unknown reach")
    return required


def components(n, centers):
    """Canonical full ambient blocks, including a distinct block per isolate."""
    parent = repair.forced_partition(n, centers)
    blocks = {}
    for v in sorted(parent):
        blocks.setdefault(repair.root(parent, v), []).append(v)
    return tuple(sorted(tuple(block) for block in blocks.values()))


def witness(s, left=False):
    """Explicit finite right-reaching maximizers; no larger board materialized."""
    n, source, _, _ = window(s, left)
    h = 3 * s
    deleted = {(h, c) for c in range(s + 3, h + 3)}
    deleted |= {v for v in source if v[0] in (h + 1, h + 2)
                and 2 <= v[1] <= h + 2}
    added = {(h - 1, s + 4)}
    added |= {(h + 1, c) for c in range(s + 1 if left else s + 2, h + 2)}
    if s == 2:
        deleted |= {(h - 3, h + 4), (h + 1, h + 4)}
        added.add((h + 1, h + 2))
    else:
        deleted.add((h - 3, h + 2))
        added.add((h - 1, h + 2))
        if not left:
            added.add((h + 2, 3))
    if left:
        deleted.add((h - 1, s + 1))
    return n, source - deleted | added


def search(s, left=False, reach="joined", node_budget=100000):
    if node_budget < 1:
        raise ValueError("node budget must be positive")
    n, source, fixed, variable = window(s, left)
    required = required_centers(s, reach)
    if not required <= fixed | variable:
        raise ValueError("required centers outside window")
    fixed |= required
    h = 3 * s
    port = (h - 3, s + 2)
    boundary = {(r, c) for r in range(n) for c in range(n)
                if r in (0, n - 1) or c in (0, n - 1)}

    def output_ok(parent):
        label = repair.root(parent, port)
        return all(repair.root(parent, b) != label for b in boundary)

    initial = repair.forced_partition(n, fixed)
    if not output_ok(initial):
        raise ValueError("mandatory occupancy already attaches output to boundary")
    best = fixed.copy()
    # A replayed old witness is a valid incumbent only in its actual class.
    _, old = two.joined_witness(s)
    if fixed <= old <= fixed | variable and output_ok(repair.forced_partition(n, old)):
        best = old
    nodes, exhaustive = 0, True

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
    assert output_ok(rebuilt) and required <= best
    assert all(repair.root(rebuilt, v) == repair.root(rebuilt, port) for v in required)
    return {"centers": best, "nodes": nodes, "exhaustive": exhaustive,
            "profile": repair.profile(n, best), "components": components(n, best)}


def main():
    for s in (2, 3):
        for left, reach in ((False, "joined"), (False, "right"),
                            (True, "joined"), (True, "left"), (True, "both")):
            n, source, _, variable = window(s, left)
            result = search(s, left, reach)
            port = (3 * s - 3, s + 2)
            output = next(b for b in result["components"] if port in b)
            print("n", n, "left", left, "reach", reach, "variables", len(variable),
                  "nodes", result["nodes"], "exhaustive", result["exhaustive"],
                  "profile", result["profile"],
                  "delete", sorted(source - result["centers"]),
                  "insert", sorted(result["centers"] - source),
                  "component_sizes", sorted(map(len, result["components"])),
                  "output", output, flush=True)


if __name__ == "__main__":
    main()

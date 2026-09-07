"""Bounded preceding-rail cut experiments, using the existing exact engine.

Only n=11 and n=14 are constructed. Importing this module runs no search.
"""

from analysis.searches import l2_rail_repair_research as repair


def preceding_cut(s):
    n, original = repair.staircase(s)
    h = 3 * s
    variable = {(r, c) for r in range(h - 1, h + 3)
                for c in range(2, h + 3)}
    cut = (h - 3, h + 2)
    return n, original, original - variable - {cut}, variable


def continuation(s):
    """Pay for an attachment cut and two cleared obstructions; extend V twice."""
    n, fixed, pieces = repair.repaired_staircase(s)
    h = 3 * s
    centers = fixed | set.union(*pieces)
    centers -= {(h - 3, h + 2), (h, s + 6), (h + 2, s + 5)}
    additions = [{(h + 1, s + 4)}, {(h + 1, s + 5)}]
    return n, centers, additions, (h + 1, s + 6)


def swept_interface(s):
    n, original = repair.staircase(s)
    h = 3 * s
    pocket = {(r, c) for r in (h + 1, h + 2) for c in range(2, h + 3)}
    fixed = original - pocket
    fixed -= {(h, c) for c in range(s + 3, h + 3)}
    fixed.remove((h - 3, h + 2))
    pieces = [{(h - 1, s + 4)},
              {(h + 1, c) for c in range(s + 1, h + 2)}]
    pieces += [{(h + 2 - t % 2, c)}
               for t, c in enumerate(range(s - 1, 2, -2))]
    return n, fixed, pieces


def main():
    for s in (2, 3):
        n, fixed, additions, blocked = continuation(s)
        centers, signatures = repair.audit_insertions(n, fixed, additions)
        parent = repair.forced_partition(n, centers)
        assert repair.insert(n, centers, parent, blocked) is None
        attachments = [blocked] + [w for w in repair.neighbors(n, blocked)
                                   if w not in centers]
        labels = [repair.root(parent, w) for w in attachments]
        print("continuation", s, repair.profile(n, centers), signatures,
              "blocked", blocked, "attachments", list(zip(attachments, labels)),
              flush=True)
        n, fixed, pieces = swept_interface(s)
        swept, _ = repair.audit_insertions(n, fixed, pieces)
        print("whole-rail-sweep", s, repair.profile(n, swept), flush=True)
        n, original, fixed, variable = preceding_cut(s)
        best, nodes = repair.maximize(n, fixed, variable)
        result = fixed | best
        assert len(result) == (48 if s == 2 else 76)
        print("preceding-cut-Q4", s, "nodes", nodes,
              "profile", repair.profile(n, result),
              "delete", sorted(original - result),
              "insert", sorted(result - original), flush=True)


if __name__ == "__main__":
    main()

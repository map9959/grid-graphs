"""All ordinary-exit 0011 charts: short folded two-gap cover with NO axis filter.

Side 35 is direct. From side 77, pin a near-end exit and insert at the
opposite end; a central exit permits independent insertions on both sides.
Only physical local catalogue covers use SAT. The two strip implementations
keep arbitrary-length, nonconstant transitions on repeated bonds.
"""
from .coupled_two_gap import keyer, local, encode
from .coupled_mask_check import check
from .folded_strip_audit import native
from .two_gap_mask_tables import VERIFIED


def main():
    counts = {}
    cache = {}
    for k in (11, 25):
        for q in range(1, k-1):
            left = k == 25 and q >= 12
            right = k == 25 and q <= 12
            gx = (8,)*left + (16,)*right
            gy = (8,) if k == 25 else ()
            keys = keyer(k, q)
            ids, tables, grid = {}, [], []
            for j in range(k-1):
                for i in range(k-1):
                    key = keys(i, j)[0]  # discard the deep-axis flags
                    if key not in cache:
                        cache[key] = local(3*k+2, q, i, j, 4, drat=True)
                    if key not in ids:
                        ids[key] = len(tables)
                        tables.append(cache[key])
                    grid.append(ids[key])
            data = encode(k, tables, grid)
            result = native(data, gx, gy, q=q)
            if not result.startswith("EMPTY"):
                raise AssertionError((k, q, result))
            if not check(1, k, (k, q), data=data, q=q, gx=gx, gy=gy):
                raise AssertionError(("independent replay", k, q))
            counts[k] = counts.get(k, 0) + 1
    print("all ordinary exits, no axis filter:", counts, "DRAT covers:", len(VERIFIED))


if __name__ == "__main__":
    main()

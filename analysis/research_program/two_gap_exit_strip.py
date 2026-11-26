"""Single vertical band for the ordinary 0011 exit. Run from repository root.

Certify the *same* five relations on both columns of every interior exit;
the two near-end exits at either end already have an empty top plaquette.
Only the middle relation is repeated by the vertical fold.
"""
from pathlib import Path
from .coupled_two_gap import keyer, local
from .coupled_mask_check import Pool, checker


def replay(write=False, verify=False):
    pool = Pool()
    cache = {}
    def relation(k, q, i, j):
        key = keyer(k, q)(i, j)[0]
        if key not in cache:
            cache[key] = pool.intern(frozenset(local(3*k+2, q, i, j, 4, drat=verify)))
        return cache[key]

    ref = [relation(25, 12, 12, j) for j in (0, 1, 2, 22, 23)]
    counts = [len(pool.items[t]) for t in ref]
    assert counts == [1, 1, 510, 342, 152]
    for k in (11, 25):
        for q in range(1, k-1):
            if q < 3 or q > k-4:
                i = q-1 if q < 3 else q
                assert not pool.items[relation(k, q, i, 0)]
                continue
            grid = [None] * (k-1)**2
            for j in range(k-1):
                target = ref[min(j, 2) if j < k-3 else 3+j-(k-3)]
                for i in (q-1, q):
                    assert relation(k, q, i, j) == target
                    grid[j*(k-1)+i] = target
            # The two physical columns are separated from either insertion
            # bond. Only row 8 can repeat; root attachment 4 is omitted.
            assert checker(k, 3, False, 0, pool, q, 16,
                           (8,) if k == 25 else ())(grid, q-1) is False
    print(f'32 charts; {len(cache)} halo keys; five nonempty tables: {counts}')
    if write or verify:
        data = [' '.join(str(sum(m << (9*i) for i, m in enumerate(w)))
                         for w in sorted(pool.items[t])) for t in ref]
        dest = Path('lean/GridGraphs/ResidueTwoUpper/Data/two_gap_exit_strip.txt')
        text = '\n'.join(data)+'\n'
        if verify:
            assert dest.read_text() == text, 'projection differs from the Lean replay input'
        if write:
            dest.write_text(text)


if __name__ == '__main__':
    import sys
    replay('--write' in sys.argv[1:], '--verify' in sys.argv[1:])

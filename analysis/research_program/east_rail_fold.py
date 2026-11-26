"""Test an east-boundary propagation lemma, not individual square sizes.

The folded column may see either itself or the neighboring column.
This relaxes overlap checks; it never identifies physical tile values.
"""
from .south_cap_seam_schedule import initial
from functools import lru_cache

LINE = {3, 7, 9, 73}


@lru_cache(maxsize=1)
def catalogue():
    return initial(40)


def probe(width, height, loop=None):
    # Reuse a sufficiently large square solely to look up the bulk-row
    # catalogue, including its seven actual eastern column tags.
    bank = catalogue()
    full = 33
    d = {(r,c): {v for v in bank[1,full-width+c]
                 if r or v[0] in LINE and v[1] in LINE}
         for r in range(height-1) for c in range(width-1)}
    while True:
        out = {}
        for (r,c),words in d.items():
            for dr,dc,a,b,i,j in [(-1,0,0,1,2,3),(1,0,2,3,0,1),
                                  (0,-1,0,2,1,3),(0,1,1,3,0,2)]:
                if (r+dr,c+dc) not in d:
                    continue
                neighbors = d[r+dr,c+dc]
                if dc and c==loop:
                    neighbors = neighbors | d[r,c]
                support = {(v[i],v[j]) for v in neighbors}
                words = {v for v in words if (v[a],v[b]) in support}
            out[r,c] = words
        if d == out: break
        d = out
    # Every tile from column 3 through the physical east boundary.
    row = [{v[0] for v in d[4,c]} for c in range(width-1)]
    row.append({v[1] for v in d[4,width-2]})
    return all(s and s <= LINE for s in row[3:])


def west_of(distance, right, height):
    """Over-approximate one column, using only its eastern neighbor
    and vertical support. Tag 6 is constant for distances >= 6."""
    words = catalogue()[1,31-min(distance,6)]
    col = [words if r else {v for v in words if v[0] in LINE and v[1] in LINE}
           for r in range(height-1)]
    if right is not None:
        for r,vs in enumerate(right):
            pairs = {(v[0],v[2]) for v in vs}
            col[r] = {v for v in col[r] if (v[1],v[3]) in pairs}
    while True:
        old = col.copy()
        for r,vs in enumerate(old):
            if r:
                pairs = {(v[2],v[3]) for v in old[r-1]}
                vs = {v for v in vs if (v[0],v[1]) in pairs}
            if r+1<len(col):
                pairs = {(v[0],v[1]) for v in old[r+1]}
                vs = {v for v in vs if (v[2],v[3]) in pairs}
            col[r] = vs
        if old==col:return col


def pump(height):
    right = None
    history = []
    for dist in range(50):
        left = west_of(dist,right,height)
        if dist>=6 and left==right:
            break
        history.append(left)
        right = left
    else:
        raise ValueError("no fixed point")
    # West crop of four plaquette columns (west of the eastern fringe).
    # Each receives its own copy of the summary: tiles are not equated.
    cols = [left.copy() for _ in range(4)]
    while True:
        previous = [col.copy() for col in cols]
        for c,col in enumerate(cols):
            for r,vs in enumerate(col):
                for dc,dr,a,b,i,j in [(1,0,1,3,0,2),(-1,0,0,2,1,3),
                                      (0,1,2,3,0,1),(0,-1,0,1,2,3)]:
                    if 0<=c+dc<4 and 0<=r+dr<len(col):
                        pairs={(v[i],v[j]) for v in previous[c+dc][r+dr]}
                        vs={v for v in vs if (v[a],v[b]) in pairs}
                col[r]=vs
        if cols==previous:break
    return dist, sorted({v[0] for v in cols[3][4]})


if __name__ == "__main__":
    for w in range(4,15):
        print("width", w, probe(w,10))
    for loop in range(4,7):
        print("width >=14, fold at", loop, probe(14,10,loop))
    print("east-to-west fixed point, row 4 column 3:",pump(10))

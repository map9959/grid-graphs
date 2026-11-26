"""Probe east-boundary rail speed, keeping the actual north path in
each tile label. Residual words are local supports, not forest witnesses."""
from .east_rail_fold import catalogue
from .south_cap_seam_schedule import seams


def down(m, n):
    # All three physical edges between the two northwest sites.
    return bool(m & 9 and m & 72 and (m & 64 or n & 1))


def across(m, n):
    return bool(m & 3 and m & 6 and (m & 4 or n & 1))


def lift(words):
    out = set()
    for a,b,c,d in words:
        for x in (False,True):
            for y in (False,True):
                z,q = x and down(a,c), y and down(b,d)
                if x and y and across(a,b) or z and q and across(c,d):
                    continue
                out.add(((a,x),(b,y),(c,z),(d,q)))
    return out


def probe(width, height):
    bank = catalogue()
    d = {}
    for c in range(width-1):
        # From the base width 33, use its bulk tag for any extra copies.
        ws = lift(bank[1,max(0,33-width+c)])
        for r in range(height-1):
            d[r,c] = ws if r else {w for w in ws if w[0]==w[1]==(73,True)}
    d,_=seams(d)
    for r in range(min(height-1,9)):
        line=[{v[0] for v in d[r,c]} for c in range(width-1)]
        line.append({v[1] for v in d[r,width-2]})
        if any(not x for x in line): raise ValueError("inconsistent probe")
        lose=max((j+1 for j,x in enumerate(line) if x!={(73,True)}),default=0)
        print(f"width={width} depth={height} row={r} rooted-73 suffix starts at {lose}",flush=True)


if __name__=="__main__":
    for w in (18,22,30):
        probe(w,10)

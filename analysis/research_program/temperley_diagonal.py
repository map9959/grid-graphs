"""Test saturated periodic fillers for a diagonal repetition of a recorded cross."""
from collections import Counter
from itertools import product
from functools import lru_cache

from .temperley_cross import geometry, grid, load, tiling


def put(d, i, j, x, y):
    p, q = (i%12,j%12), ((i+x)%12,(j+y)%12)
    assert p not in d and q not in d
    d[p], d[q] = (x,y),(-x,-y)


def saturated():
    """All saturated doubled 12x12 torus matchings, global primal parity even."""
    for phase in range(3):
        for signs in product((-1,1), repeat=4):
            d = {}
            for r,c in grid(6):
                band, depth = divmod((r-phase)%6,3)
                # Primal rails at depth 0. Dual rails between depths 1 and 2.
                if depth == 0:
                    put(d,2*r,2*c,0,signs[band])
                else:
                    put(d,2*r,2*c,(-1 if depth==1 else 1),0)
                if depth == 1:
                    put(d,2*r+1,2*c+1,0,signs[2+band])
                else:
                    put(d,2*r+1,2*c+1,(1 if depth==0 else -1),0)
            assert len(d) == 144
            yield d
            yield {(j,i):(y,x) for (i,j),(x,y) in d.items()}


def sides(get, a, b):
    """Four bitmasks of outward dominoes, indexed by increasing coordinate."""
    lines = [
        [(a,b+k,-1,0) for k in range(12)],
        [(a+k,b+11,0,1) for k in range(12)],
        [(a+11,b+k,1,0) for k in range(12)],
        [(a+k,b,0,-1) for k in range(12)],
    ]
    return tuple(sum(1<<k for k,(i,j,x,y) in enumerate(line) if get(i,j)==(x,y))
                 for line in lines)


def libraries():
    lib = {}
    for a,b in grid(2):
        profiles = Counter()
        for d in saturated():
            n,e,s,w = sides(lambda i,j: d[i%12,j%12],a,b)
            assert n==s and e==w
            profiles[n,e] += 1
        lib[a,b] = profiles
    return lib


@lru_cache(None)
def connector(height, width, ports, initial=()):
    """Exact bipartite matching with prescribed external ports, returning a witness."""
    cells = {(i,j) for i in range(height) for j in range(width)}
    d = {}
    for i,j,x,y in ports:
        if (i,j) in d:
            return None
        assert (i+x,j+y) not in cells
        d[i,j] = x,y
    inside = cells-d.keys()
    black = sorted(p for p in inside if sum(p)%2==0)
    if 2*len(black)!=len(inside):
        return None
    match = {q:p for p,q in initial if p in inside and q in inside}
    already = set(match.values())
    def augment(p,seen):
        i,j = p
        for x,y in ((0,1),(1,0),(-1,0),(0,-1)):
            q = i+x,j+y
            if q in inside and q not in seen:
                seen.add(q)
                if q not in match or augment(match[q],seen):
                    match[q] = p
                    return True
        return False
    for p in black:
        if p not in already and not augment(p,set()):
            return None
    for (i,j),(a,b) in match.items():
        d[i,j],d[a,b] = (a-i,b-j),(i-a,j-b)
    assert cells==d.keys()
    return d


def arm_options(d, a, b, witnesses=False, preserve=False):
    result = []
    for r,c,h,w,horiz in [(0,b,a,12,True),(a+12,b,21-a,12,True),
                           (a,0,12,b,False),(a,b+12,12,21-b,False)]:
        ports = []
        for i,j in product(range(h),range(w)):
            x,y = d[r+i,c+j]
            if not (0 <= i+x < h and 0 <= j+y < w):
                ports.append((i,j,x,y))
        opts = []
        for sign in [-1,1]:
            copied = []
            for i,j,x,y in ports:
                axis = y if horiz else x
                if not axis:
                    copied.append((i,j,x,y))
                if axis == sign:
                    copied.append((i,j,x,y))
                    copied.append((i,w-1-j,0,-y) if horiz else (h-1-i,j,-x,0))
            initial = []
            if preserve:
                for i,j in product(range(h),range(w)):
                    x,y = d[r+i,c+j]
                    if (i+j)%2==0 and 0<=i+x<h and 0<=j+y<w:
                        initial.append(((i,j),(i+x,j+y)))
            tile = connector(h,w,tuple(sorted(copied)),tuple(initial))
            opts.append(tile if witnesses else tile is not None)
        result.append(tuple(opts))
    return tuple(result)


def fixed_family(t):
    """Replay one predetermined diagonal template, never search a larger board."""
    from .temperley_cross import score
    a,b = 9,1
    edges = geometry(17)
    centers = {(2*i,2*j) for i,j in load()}
    forced = {m for m,(p,_) in edges.items() if centers.intersection(p)}
    d = tiling(edges,forced|{(3,4)},(0,0))
    n,e,s,w = sides(lambda i,j:d[i,j],a,b)
    fillers = []
    for ns,ew in [(n,e),(s,w)]:
        for tile in saturated():
            get = lambda i,j:tile[i%12,j%12]
            if sides(get,a,b) == (ns,ew,ns,ew):
                fillers.append({(i,j):get(a+i,b+j) for i,j in grid(12)})
                break
    opts = arm_options(d,a,b,True,True)
    def kind(k):
        return 0 if k==0 else 2 if k==t+1 else 1
    heights,widths = [a]+[12]*t+[21-a], [b]+[12]*t+[21-b]
    board = {}
    for i,h in enumerate(heights):
        for j,width in enumerate(widths):
            ri,cj = kind(i),kind(j)
            r,c = (0,a,a+12)[ri],(0,b,b+12)[cj]
            src = None
            if ri==cj==1 and i!=j:
                src = fillers[int(i>j)]
            elif (ri==1)!=(cj==1):
                arm, pos = ((0 if ri==0 else 1),j) if cj==1 else ((2 if cj==0 else 3),i)
                left,right = opts[arm]
                if left is not None and pos!=t:
                    src = left
                if left is None and pos!=1:
                    assert right is not None
                    src = right
            dr,dc = sum(heights[:i]),sum(widths[:j])
            for y,x in product(range(h),range(width)):
                if src is not None:
                    board[dr+y,dc+x] = src[y,x]
                elif (r+y,c+x) in d:
                    board[dr+y,dc+x] = d[r+y,c+x]
    side = 21+12*t
    assert len(board)==side**2-1
    assert all(board.get((i+x,j+y))==(-x,-y) for (i,j),(x,y) in board.items())
    return score(board,side)


def census():
    edges = geometry(17)
    centers = {(2*i,2*j) for i,j in load()}
    forced = {m for m,(p,_) in edges.items() if centers.intersection(p)}
    lib = libraries()
    histogram = Counter()
    full = Counter()
    balances = Counter()
    adapters = Counter()
    example = {}
    target_hist = Counter()
    from .temperley_cross import crop, score
    for bridge,root in product(((3,4),(4,3),(4,5),(5,4)), product((0,32),repeat=2)):
        d = tiling(edges,forced|{bridge},root)
        for a,b in product(range(1,21),repeat=2):
            n,e,s,w = sides(lambda i,j: d[i,j],a,b)
            profiles = lib[a%2,b%2]
            def distance(x,y):
                return min((x^p).bit_count()+(y^q).bit_count() for p,q in profiles)
            # Both possible directions of the moving diagonal.
            ds = [(distance(n,e),distance(s,w)), (distance(n,w),distance(s,e))]
            best = min(sum(p) for p in ds)
            histogram[best] += 1
            example.setdefault(best,(bridge,root,a,b,ds))
            if best == 0:
                # The outer side of an arm is physical boundary. Equal end
                # ports cancel in checkerboard balance since the period is even.
                imbalance = tuple(sum((-1)**k for k in range(12) if mask>>k&1)
                                  for mask in (n,e,s,w))
                balances[tuple(sorted(map(abs,imbalance)))] += 1
                opts = arm_options(d,a,b)
                ok = sum(map(any,opts))
                adapters[ok] += 1
                example.setdefault(("adapter",ok),(bridge,root,a,b,ds,opts))
                arm_bad = sum((d.get((i,b))==(0,-1)) != (d.get((i,b+11))==(0,1))
                              for i in range(33) if not a<=i<a+12)
                arm_bad += sum((d.get((a,j))==(-1,0)) != (d.get((a+11,j))==(1,0))
                               for j in range(33) if not b<=j<b+12)
                full[arm_bad] += 1
                example.setdefault(("arm",arm_bad),(bridge,root,a,b,ds))
            # Only a singleton repair can qualify for the previous target set.
            small = crop(d,a,b)
            free = [(i,j) for (i,j),(x,y) in small.items()
                    if small.get((i+x,j+y))!=(-x,-y)]
            if len(free)==2:
                (i,j),(p,q) = free
                if abs(p-i)+abs(q-j)==1:
                    small[i,j],small[p,q]=(p-i,q-j),(i-p,j-q)
                    if score(small,21)==48:
                        target_hist[tuple(ds)] += 1
    return histogram, target_hist, full, balances, adapters, example


if __name__ == "__main__":
    all_cuts, targets, arms, balances, adapters, examples = census()
    print("minimum total port disagreements, best diagonal:",sorted(all_cuts.items()))
    print("one-domino target cuts, paired distances for each diagonal:",targets)
    print("best cut:",examples[min(all_cuts)])
    print("unmatched arm ports for exact center joins:",sorted(arms.items()))
    print("best arms:",examples["arm",min(arms)])
    print("absolute arm checkerboard imbalances:",balances)
    print("number of repeatable adapted arms:",adapters)
    print("best adapted witness:",examples["adapter",max(adapters)])
    print("fixed adapter family scores:",[fixed_family(t) for t in range(1,5)])

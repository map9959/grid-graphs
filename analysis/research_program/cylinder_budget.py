"""Use width-independent cylinder distances to settle regional gain budgets."""
from collections import Counter, defaultdict, deque
from pathlib import Path
import subprocess

from .alternating_invoice import bound
from .diagonal_cylinder import cross, mid, transitions
from .temperley_diagonal import saturated, sides


def state(tile,d):
    v,h=cross(tile,d-1)
    pv,_=cross(tile,d-2)
    return v|(h>>1)|((h&1)<<11),v,mid(pv,v)


def run_lines(lines):
    binary=Path(__file__).resolve().parents[2]/"target/release/diagonal_budget"
    out=subprocess.run([binary],input="\n".join(lines),text=True,capture_output=True,check=True)
    records=[list(map(int,line.split())) for line in out.stdout.splitlines()]
    assert len(records)==len(lines)
    return records


def controls():
    # Cut a horizontal domino pair on either side of the FINAL slice.
    # A single elementary flip gives a nonperiodic destination with a
    # known finite path. Compute its true cost directly from primal degrees.
    lines=[];expected=[]
    for tile in saturated():
        lines.append(" ".join(map(str,[*state(tile,-24),0,*state(tile,26)])))
        expected.append(0)
        occ,_,prev=state(tile,-24)
        choices=[]
        for v,_,occ2 in transitions(occ):
            for w,_,end in transitions(occ2):
                nxt=mid(v,w)
                degs=[sum(mask>>(j%12)&1 for mask,j in
                          ((prev,c),(prev,c+1),(nxt,c),(nxt,c-1))) for c in range(0,12,2)]
                cost=sum(n-1 for n in degs if n<4)
                if cost in (1,2):
                    choices.append((cost,end,w,nxt))
        if choices:
            cost,*end=min(choices)
            lines.append(" ".join(map(str,[*state(tile,-24),cost,*end])))
            expected.append(cost)
        for i in range(12):
            j=(i-1)%12
            if tile[i,j]!=tile[(i+1)%12,j] or tile[i,j]!=(0,1):
                continue
            alt=dict(tile)
            for c in [j,(j+1)%12]:
                alt[i,c]=(1,0)
                alt[(i+1)%12,c]=(-1,0)
            # Flip only near d=25, not periodically in the normal direction.
            class Joined:
                def __getitem__(self,p):
                    r,c=p
                    return (alt if 24<=r-c<=26 else tile)[r%12,c%12]
            joined=Joined()
            def outgoing(d):
                return tuple(sum(1<<c for c in range(12) if joined[d+c,c]==move)
                             for move in ((1,0),(0,-1)))
            v,h=outgoing(25);pv,_=outgoing(24)
            end=v|h>>1|(h&1)<<11,v,mid(pv,v)
            cost=0
            for d in range(-12,13):
                for c in range(6):
                    r=d+c
                    deg=sum((2*r+x+joined[2*r+x,2*c+y][0])%2==0
                            for x,y in ((1,0),(-1,0),(0,1),(0,-1)))
                    cost+=(deg-1 if deg<4 else 0)
            assert cost>=0
            if end!=state(tile,26) and cost<=2:
                lines.append(" ".join(map(str,[*state(tile,-24),cost,*end])))
                expected.append(cost)
                break
    result=run_lines(lines)
    assert all(d<=k for (_,d),k in zip(result,expected))
    print("positive control paths:",len(result),"direct path costs:",dict(Counter(expected)))


def audit_distances():
    rows=[d for d in saturated() if all(not sum((-1)**h for h in range(12) if m>>h&1)
                                        for m in sides(lambda i,j:d[i%12,j%12],4,4)[:2])]
    ends=[x for d in rows for x in state(d,26)]
    results=run_lines([" ".join(map(str,[*state(d,-24),2,*ends])) for d in rows])
    distances=Counter(v for _,*tail in results for v in tail)
    assert all((v==0)==(i==j) for i,row in enumerate(results) for j,v in enumerate(row[1:]))
    print("centered background distances (255 means >2 or unreachable):",dict(distances))

    # Independent zero-loss reachability: tuple members are explicit
    # bitmasks, with scalar degree checks instead of Rust bit-sliced cost.
    root=(*state(rows[0],-24),0)
    seen={root}; todo=deque([root])
    while todo:
        occ,_,prev,phase=todo.popleft()
        for v,_,o2 in transitions(occ):
            for w,_,end in transitions(o2):
                nxt=mid(v,w)
                if all(sum(mask>>(j%12)&1 for mask,j in
                           ((prev,c),(prev,c+1),(nxt,c),(nxt,c-1))) in (1,4)
                       for c in range(0,12,2)):
                    dest=end,w,nxt,(phase+1)%6
                    if dest not in seen:
                        seen.add(dest);todo.append(dest)
    ((rust_count,*rust_dist),)=run_lines([" ".join(map(str,[*root[:3],0,*ends]))])
    assert len(seen)==rust_count and all(((*state(d,26),1) in seen)==(v==0)
                                         for d,v in zip(rows,rust_dist))
    print("independent zero-loss traversal:",len(seen),"states, all 36 exit tests agree")


def check(offset,a=4,bcol=4,slack=0):
    b={}
    bound(a,bcol,offset,2,True,slack=slack,flux_only=True,budgets=b)
    rows=[d for d in saturated()
          if all(not sum((-1)**h for h in range(12) if m>>h&1)
                 for m in sides(lambda i,j:d[i%12,j%12],a,bcol)[:2])]
    assert len(rows)==36
    targets=defaultdict(list)
    for (i,j),k in b.items():
        if k>=0:
            targets[i].append((j,k))
    lines=[]
    for i,pairs in targets.items():
        # Reference lower cut primal d=-12, upper cut just past d=12.
        vals=[*state(rows[i],-24),max(k for _,k in pairs)]
        for j,_ in pairs:
            vals.extend(state(rows[j],26))
        lines.append(" ".join(map(str,vals)))
    survivors=[];sizes=[]
    for (i,pairs),(size,*ds) in zip(targets.items(),run_lines(lines)):
        sizes.append(size)
        assert len(ds)==len(pairs)
        for (j,k),d in zip(pairs,ds):
            if d<=k:survivors.append((i,j,k,d))
    print("offset",offset,"budget distribution",dict(Counter(k for pairs in targets.values() for _,k in pairs)),
          "sources",len(sizes),"reached state counts",sorted(set(sizes)),
          "target survivors",survivors,flush=True)
    return survivors


if __name__=="__main__":
    import argparse
    p=argparse.ArgumentParser()
    p.add_argument("--all-splits",action="store_true")
    args=p.parse_args()
    controls()
    audit_distances()
    splits=[(a,b) for a in range(1,9) for b in range(a,9)] if args.all_splits else [(4,4)]
    total=sum(len(check(o,a,b)) for a,b in splits for o in (0,1))
    print("splits:",len(splits),"parities: 2","target transitions:",total)

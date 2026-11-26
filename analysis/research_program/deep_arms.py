"""Bound retiled boundary arms via a loss threshold, independent of the column DP."""
from .temperley_synthesis import Formula,solve
from .period_nine import backgrounds,profile,arm


def formula(d,h,side,last):
    n=18
    def get(i,j):
        r=i if side in ('top','left') else last-i
        c=j
        if side in ('left','right'):r,c=c,r
        x,y=d[r%n,c%n]
        if side in ('left','right'):x,y=y,x
        return (-x if side in ('bottom','right') else x),y
    f=Formula()
    def edge(i,j,direction):
        v,w=direction
        p=(i,j%n)
        q=(i+v,(j+w)%n)
        if q[0]<0:return False
        if i>=h:return get(i,j)==direction
        if q[0]>=h:return get(*q)==(-v,-w)
        return f.var(tuple(sorted((p,q))))
    dirs=[(1,0),(0,1),(-1,0),(0,-1)]
    for i in range(h):
        for j in range(n):
            ls=[edge(i,j,e) for e in dirs]
            vs=[v for v in ls if isinstance(v,str)]
            if True in ls:
                for v in vs:f.clause(f"(not {v})")
            else:
                f.clause(*vs)
                for a,v in enumerate(vs):
                    for w in vs[:a]:f.clause(f"(not {v})",f"(not {w})")
    end=h+h%2+2
    # Cut past even doubled row end: all arrows crossing it come from known sites.
    flux=sum((get(end+2,j)==(-1,0))-(get(end,j)==(1,0)) for j in range(0,n,2))
    K=9*(end//2+1)+flux+9
    scores=[]
    for i in range(0,end+1,2):
        for j in range(0,n,2):
            wrong=[]
            for v,w in dirs:
                if i+v<0:continue
                # A midpoint paired along the perpendicular axis is dual.
                wrong.extend(edge(i+v,j+w,(x,y)) for x,y in dirs if v*x+w*y==0)
            if True in wrong:continue
            vs=[v for v in wrong if isinstance(v,str)]
            if not vs:
                K-=3
                continue
            s=f.var(("score",i,j))
            for v in vs:f.clause(f"(not {s})",f"(not {v})")
            scores.append(s)
    return f,K,scores


def query(d,h,side,last,threshold,seconds):
    f,K,scores=formula(d,h,side,last)
    need=(K-threshold+2)//3
    f.pb({s:1 for s in scores},need)
    return solve(f.smt(),seconds)[0]


_bounds={}
statuses={}
def lower_bound(d,h,side,last,seconds=10):
    pf=profile(d,h,side,last,18)
    if sum((-1)**j for j,(p,_) in enumerate(pf) if p):return 1000
    key=h,pf
    if key not in _bounds:
        f,K,scores=formula(d,h,side,last)
        lo=K%3
        for test in range(lo,10,3):
            need=(K-test+2)//3
            g=Formula();g.pb({s:1 for s in scores},need)
            ans=solve(f.smt()+"\n"+"\n".join(g.clauses),seconds)[0]
            statuses[ans]=statuses.get(ans,0)+1
            if ans!='unsat':break
            lo+=3
        _bounds[key]=lo
    return _bounds[key]


def arbitrary():
    from collections import Counter
    from pathlib import Path
    import subprocess
    jobs={}
    blocked=Counter()
    for res in range(3):
        last=8+6*res
        for d in backgrounds():
            for side in ('top','right','bottom','left'):
                lb=lower_bound(d,14,side,last)
                if lb==1000:
                    blocked[res]+=1
                    continue
                def get(i,j):
                    r=i if side in ('top','left') else last-i
                    c=j
                    if side in ('left','right'):r,c=c,r
                    x,y=d[r%18,c%18]
                    if side in ('left','right'):x,y=y,x
                    return (-x if side in ('bottom','right') else x),y
                occ=sum(1<<j for j in range(18) if get(0,j)==(1,0))
                prev=sum(1<<j for j in range(0,18,2) if get(1,j)[1]==0)
                # Cut just beyond doubled row H=18m, m>0. All crossing
                # primal arrows have fixed directions. K=9(H/2+1)+flux+9.
                flux=sum((get(2,j)==(-1,0))-(get(0,j)==(1,0)) for j in range(0,18,2))
                assert (lb-flux)%3==0
                def rot(x,s):return ((x<<s)|(x>>(18-s)))&((1<<18)-1)
                k=min((rot(occ,s),rot(prev,s)) for s in range(0,18,2))
                jobs.setdefault((*k,lb),Counter())[res]+=1
    binary=Path(__file__).resolve().parents[2]/'target/release/arm_depth'
    tests=[(i,j,v) for i,j,v in jobs if v>=3]
    lines=[' '.join(map(str,(i,j,v-3,id_))) for id_,(i,j,v) in enumerate(tests)]
    out=subprocess.run([binary],input='\n'.join(lines),text=True,capture_output=True,check=True)
    reached=[]
    for idx,(key,line) in enumerate(zip(tests,out.stdout.splitlines(),strict=True)):
        nr,found,count=map(int,line.split())
        assert nr==idx and found==key[2]-2,(key,found,count)
        reached.append(count)
    print("normal transfer start/cost classes",len(jobs),"positive threshold tests",len(tests),
          "max reached states",max(reached),"improvements",0)
    for r in range(3):
        h=Counter()
        for (_,_,lb),counts in jobs.items():h[lb]+=counts[r]
        print("residue",r,"arbitrary-depth arm lower bounds",dict(sorted(h.items())),"unbalanced",blocked[r])


if __name__=='__main__':
    import sys
    if '--arbitrary' in sys.argv:
        arbitrary()
        sys.exit()
    from collections import Counter
    ds=list(backgrounds());seen=set();out=Counter()
    for d in ds:
        pf=profile(d,8,'top',8,18)
        if pf in seen or sum((-1)**j for j,(p,_) in enumerate(pf) if p):continue
        seen.add(pf)
        v=arm(8,pf)
        for test in [v-1,v]:
            ans=query(d,8,'top',8,test,8)
            assert ans==('unsat' if test<v else 'sat'),(v,test,ans)
            out[ans]+=1
    print("arm transfer vs independent PB thresholds:",dict(out))

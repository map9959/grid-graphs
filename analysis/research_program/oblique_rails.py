"""Period (3,6): transfer normal to 2r-c on a six-site doubled slice."""
from collections import Counter,deque
from functools import lru_cache
from .period_nine import budgets


def bits(d,z,condition):
    return sum(1<<r for r in range(6) if condition(d[r%12,(2*r-z)%12]))


def cut(d,z=0):
    vertical=lambda v:v[0]!=0
    history=tuple(bits(d,z-i,vertical)&(42 if (z-i)%2==0 else 21) for i in (4,3,2,1))
    v=bits(d,z,lambda q:q==(-1,0))
    h=bits(d,z,lambda q:q==(0,1))
    later=bits(d,z-1,lambda q:q==(1,0))
    return v,h,((later<<1)&63)|(later>>5),history,z%12


@lru_cache(None)
def moves(v,h,later):
    assert not v&h
    free=63^(v|h)
    out=[]
    up=free
    while True:
        across=free^up
        if not across&later:
            out.append((later,across,((up<<1)&63)|(up>>5),v|up))
        if up==0:break
        up=(up-1)&free
    return out


def successors(s):
    v,h,later,history,phase=s
    for vv,hh,nn,vertical in moves(v,h,later):
        loss=0
        if phase%2==0:
            for r in (0,2,4):
                degree=((history[0]>>((r-1)%6))&1)+((vertical>>((r+1)%6))&1)
                degree+=2-((history[1]>>r)&1)-((history[3]>>r)&1)
                assert degree>=1
                if degree<4:loss+=degree-1
        yield (vv,hh,nn,history[1:]+(vertical&(42 if phase%2==0 else 21),),(phase+1)%12),loss


def closure(source,limit):
    dist={source:0}
    q=deque([source])
    while q:
        s=q.popleft();k=dist[s]
        for target,w in successors(s):
            if k+w<=limit and dist.get(target,limit+1)>k+w:
                dist[target]=k+w
                q.append(target)
    return dist


def arbitrary_arms(rows,res):
    import subprocess
    from pathlib import Path
    jobs={}
    for i,d,c in rows:
        for s,side in enumerate(('top','right','bottom','left')):
            if c[s]>=1000:continue
            def get(i,j):
                r=i if side in ('top','left') else 8+6*res-i
                if side in ('left','right'):r,j=j,r
                x,y=d[r%12,j%12]
                if side in ('left','right'):x,y=y,x
                return (-x if side in ('bottom','right') else x),y
            occ=sum(1<<j for j in range(12) if get(0,j)==(1,0))
            mid=sum(1<<j for j in range(0,12,2) if get(1,j)[1]==0)
            flux=sum((get(2,j)==(-1,0))-(get(0,j)==(1,0)) for j in range(0,12,2))
            assert (c[s]-flux)%3==0
            if c[s]>=3:jobs.setdefault((occ,mid,c[s]),[]).append((i,s))
    binary=Path(__file__).resolve().parents[2]/'target/release/arm_depth'
    lines=[' '.join(map(str,(o,m,v-3,k))) for k,(o,m,v) in enumerate(jobs)]
    result=subprocess.run([binary,'--six'],input='\n'.join(lines),text=True,capture_output=True,check=True)
    out={i:c.copy() for i,d,c in rows}
    for idx,(key,line) in enumerate(zip(jobs,result.stdout.splitlines(),strict=True)):
        _,_,v=key
        k,best,_=map(int,line.split());assert k==idx
        if best<=v-3:
            for i,s in jobs[key]:out[i][s]=best
    print("residue",res,"all-depth arm costs vs previous:",
          dict(Counter((x,y) for i,d,c in rows for x,y in zip(c,out[i]))))
    return [(i,d,out[i]) for i,d,_ in rows]


def census():
    cases=[]
    sources={}
    for res in (0,1):
        rows=[(i,d,c) for i,d,c in budgets(6,res)
              if all(d[r,c]==d[(r+6)%12,c] for r,c in d)]
        assert len(rows)==60
        rows=arbitrary_arms(rows,res)
        for z in (0,1,2):
            pairs=[]
            for i,d,a in rows:
                for j,e,b in rows:
                    loss=4*a[0]+4*b[2]+z*a[3]+(4-z)*b[3]+(z+2)*a[1]+(2-z)*b[1]
                    budget=(24-loss)//4
                    if budget>=0:
                        pairs.append((i,j,budget))
                        sources[i]=max(sources.get(i,0),budget)
            cases.append((res,z,pairs))
    tiles={i:d for i,d,c in rows}
    states={i:cut(d) for i,d in tiles.items()}
    for d in tiles.values():
        for z in range(12):
            assert (cut(d,z+1),0) in successors(cut(d,z))
    print("homogeneous seam controls:",len(tiles)*12,flush=True)
    results={}
    for i,b in sources.items():
        dist=closure(states[i],b)
        results[i]={j:dist.get(s,999) for j,s in states.items()}
        print("source",i,"budget",b,"states",len(dist),flush=True)
    for res,z,pairs in cases:
        passed=[(i,j,b) for i,j,b in pairs if results[i][j]<=b]
        print("residue",res,"intercept",z,"/ 4","budgets",dict(Counter(b for i,j,b in pairs)),
              "survivors",passed,flush=True)
    return cases,results


def seam_costs(cap=3):
    """Cross-check the packed transfer and measure each budget-relevant join."""
    import subprocess
    from pathlib import Path
    rows=budgets(6,0)
    def compressed(d):
        v,h,l,m,_=cut(d)
        hist=sum(((mask>>(2*j+1-z%2))&1)<<(3*z+j) for z,mask in enumerate(m) for j in range(3))
        return [v,h,l,hist]
    ids=[6,24,39];ends=[24,25,38,56,75]
    binary=Path(__file__).resolve().parents[2]/"target/release/oblique_cost"
    for limit in (1,cap):
        for i in ids:
            data=[limit,*compressed(rows[i][1])]
            for j in ends:data.extend(compressed(rows[j][1]))
            out=subprocess.run([binary],input=' '.join(map(str,data)),text=True,capture_output=True,check=True)
            size,*ds=map(int,out.stdout.split())
            if limit==1:
                states=closure(cut(rows[i][1]),limit)
                assert size==len(states) and ds==[states.get(cut(rows[j][1]),255) for j in ends]
            print("source",i,"cost limit",limit,"states",size,"destinations",
                  dict(zip(ends,ds)),flush=True)


if __name__=="__main__":
    census()
    seam_costs()

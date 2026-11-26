"""Eliminate primal arrows using the grounded depth-two teeth and symmetric bulk joins."""
from functools import lru_cache
from hashlib import file_digest
from itertools import product,combinations
from pathlib import Path
import subprocess,sys
from .defect_window import DIR,table
from .odd_frames import frame
from .tight_corner_sat import cover
from .extend_forest_28 import verify

def run(n,seconds,dual=0):
    from pysat.card import CardEnc
    assert n>=119 and n%42==35
    typ,P,S=table(n)
    dep=lambda i,j:min(i,j,n-1-i,n-1-j)
    bit=lambda i,j:1+i*n+j
    words=[(0,*w) for w in product((1,3),repeat=3)]
    frames=[frame(n,w) for w in words]
    par={(0,0):-1};Q=list(par)
    for i,j in Q:
        for d,(a,b) in enumerate(DIR):
            u=i+a,j+b
            if dep(*u)==0 and u not in par and (frames[0][i,j] or frames[0][u]):
                par[u]=(d+2)%4;Q.append(u)
    assert len(Q)==4*n-4
    stem=Path(f'target/depth_two_marks_{n}_{dual}');fn=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
    f=fn.open('w');f.write(' '*90+'\n');nc=0
    def add(*lits):
        nonlocal nc
        f.write(' '.join(map(str,lits))+' 0\n');nc+=1
    sels=[n*n+1+k for k in range(8)];add(*sels);top=sels[-1]
    for u in frames[0]:
        ls=[bit(*u)*(1 if m[u] else -1) for m in frames]
        if len(set(ls))==1:add(ls[0])
        else:
            for a,z in zip(sels,ls):add(-a,z)
    flags={}
    for d in range(5,n-5,3):
        for p in ((2,d),(d,2)):
            top+=1;flags[p]=top
    card=CardEnc.equals(list(flags.values()),1,top_id=top,encoding=1);top=card.nv
    for c in card.clauses:add(*c)
    @lru_cache(None)
    def masks(bad):
        return [[(s,-1 if v>>s&1 else 1) for s in range(len(bad).bit_length()-1) if m>>s&1] for m,v in cover(bad)]
    def forbid(bits,bad,guard=()):
        for c in masks(bad):add(*guard,*(bits[s]*v for s,v in c))
    @lru_cache(None)
    def bulk(t):
        ds=tuple(range(4));tabs=[S(t,ds,d,False,False) for d in ds]
        sinks=S(t,ds,-1,True,False)  # request raw sinks, not an admissible second root
        allowed=[z[1]==0 for z in tabs]
        for d,z in enumerate(tabs):
            for m in range(32):
                if any(m&(2<<e) and m&(2<<((e+1)%4)) for e in ds):continue
                if m&1:assert sinks[m]==576
                if not (m&1 or m&(2<<d)):continue
                assert (z[m]==0)==bool(not m&1 or m&(2<<d) or allowed[d])
        return allowed
    @lru_cache(None)
    def patch(t):return tuple(q!=0 for q in P(t))
    @lru_cache(None)
    def shellmask(t,ds,layer,pout,feet,pernb,iso):
        bad=[]
        for m in range(1<<(len(ds)+1)):
            marked=m&1;nb=[d for h,d in enumerate(ds) if m&(2<<h)]
            q=0
            if not layer:o=pout
            elif layer==2 and marked:o=feet[0] if len(feet)==1 else -2
            elif len(nb)==1:o=nb[0]
            elif layer==1 and not marked and len(nb)==2 and len(set(nb)&set(pernb))==1:o=next(iter(set(nb)&set(pernb)))
            elif layer==2 and not marked and not nb and iso:o=-1;q=72
            else:o=-2
            bad.append(o==-2 or S(t,ds,o,(layer==0 and pout==-1),len(ds)==2)[m]!=q)
        return tuple(bad)
    forbidden=0;bulktypes=set();jtypes=set()
    for i,j in product(range(n),repeat=2):
        u=(i,j);layer=dep(*u);v=bit(*u)
        ds=tuple(d for d,(a,b) in enumerate(DIR) if dep(i+a,j+b)>=0)
        nb=[bit(i+DIR[d][0],j+DIR[d][1]) for d in ds];bits=[v,*nb]
        if max(i,j)<n-2:forbid([bit(i+a,j+b) for a,b in product(range(3),repeat=2)],patch(typ(1,i,j)))
        if u in flags:
            for z in bits:add(-flags[u],-z)
            add(*bits,flags[u])
        else:add(*bits)
        if layer<3:
            pernb=tuple(d for d in ds if dep(i+DIR[d][0],j+DIR[d][1])==0)
            tables=[]
            for m in frames:
                feet=tuple(d for d,(a,b) in enumerate(DIR) if layer==2 and dep(i+2*a,j+2*b)==0 and m[i+2*a,j+2*b])
                if layer==2:assert feet
                tables.append(shellmask(typ(0,i,j),ds,layer,par.get(u,-2),feet,pernb,u in flags))
            if len(set(tables))==1:forbid(bits,tables[0])
            else:
                for a,bad in zip(sels,tables):forbid(bits,bad,(-a,))
        else:
            t=typ(0,i,j);bulktypes.add(t);allow=bulk(t)
            add(-v,*nb,*(bit(i+2*a,j+2*b) for d,(a,b) in enumerate(DIR) if allow[d]))
        for d,(a,b) in enumerate(DIR[:2]):
            x,y=i+2*a,j+2*b;l=dep(x,y)
            if layer==2 and dep(i+a,j+b)==2:add(-v,-bit(i+a,j+b))
            if min(layer,l)<2:continue
            ok=layer>2 and bulk(typ(0,i,j))[d]
            rev=l>2 and bulk(typ(0,x,y))[d+2]
            if min(layer,l)>=3:
                assert ok==rev
                jtypes.add((typ(0,i,j),d,typ(0,x,y)))
            if not (ok or rev):
                add(-v,bit(i+a,j+b),-bit(x,y));forbidden+=1
    if dual in (2,3,4,7):
        from .grounded_lines import install
        top=install(n,top,bit,add)
    if dual==4:
        # One start per straight run. A target has exactly this many;
        # this relaxation needs only the upper half of the equality.
        from pysat.pb import PBEnc,EncType
        starts=[]
        for i,j in product(range(n),repeat=2):
            top+=1;starts.append(top);z=bit(i,j)
            prev=([bit(i-1,j)] if i else [])+([bit(i,j-1)] if j else [])
            add(-z,*prev,top);add(-top,z)
            for p in prev:add(-top,-p)
        c=PBEnc.atmost(lits=starts,bound=8*n//7-2,top_id=top,encoding=EncType.adder)
        for cl in c.clauses:add(*cl)
        top=c.nv
    if dual in (7,8):
        from pysat.pb import PBEnc,EncType
        losses=[];k=(n-2)//3;U=3*k*k+7*k-(k-5)//7
        for i,j in product(range(1,n-1,3),repeat=2):
            bits=[bit(i+a,j+b) for a,b in product(range(3),repeat=2)]
            # The aligned blocks have 1..3 marks. The corner blocks
            # have at most two. See aligned_tile_bound.py for the independent check.
            for h in (1,2):
                top+=1;losses.append(top)
                for cs in combinations(bits,9-h):add(*cs,top)
                for cs in combinations(bits,h+1):add(*(-z for z in cs),-top)
        deficit=3*k*k-U+4*n-9
        c=PBEnc.equals(lits=losses,bound=deficit,top_id=top,encoding=EncType.adder)
        for cl in c.clauses:add(*cl)
        top=c.nv
    if dual in (5,6):
        from .run_owners import install
        top=install(n,top,bit,add,par)
    if dual in (1,3,6,8):
        m=n-1;base=top
        def var(i,j,d):return base+5*(i*m+j)+1+d
        for i,j in product(range(m),repeat=2):
            ds=[d for d,(a,b) in enumerate(DIR) if 0<=i+a<m and 0<=j+b<m]
            arcs=[var(i,j,d) for d in ds]
            if (i,j)==(0,1):
                for z in arcs:add(-z)
            else:add(*arcs)
            for a,b in combinations(arcs,2):add(-a,-b)
            for d,(a,b) in enumerate(DIR):
                if d not in ds:continue
                x,y=i+a,j+b;z=var(i,j,d);w=var(x,y,(d+2)%4)
                if d<2:
                    p=(i+a,j+b);q=(i+1,j+1) # vertical primal edge for d=0
                    exc=flags.get(q) if (d==0 and q[0]==2 or d==1 and q[1]==2) else None
                    add(-z,-w);add(bit(*p),bit(*q),z,w,*([exc] if exc else []))
                    for end in (p,q):add(-z,-bit(*end));add(-w,-bit(*end))
                    if exc:add(-exc,-z);add(-exc,-w)
                if (x,y)==(0,1) or dual==6:continue
                h,k=var(i,j,4),var(x,y,4);e={0:3,3:0}.get(d)
                if e is None or not(0<=x+DIR[e][0]<m and 0<=y+DIR[e][1]<m):
                    add(-z,-h,k);add(-z,h,-k)
                else:
                    w=var(x,y,e)
                    add(-z,w,-h,k);add(-z,w,h,-k);add(-z,-w,-h,-k);add(-z,-w,h,k)
        top+=5*m*m
    f.seek(0);f.write(f'p cnf {top} {nc}'.ljust(90));f.close()
    with fn.open('rb') as src:print('bulk types',len(bulktypes),'symmetric join types',len(jtypes),'forbidden hops',forbidden,'vars',top,'clauses',nc,'sha256',file_digest(src,'sha256').hexdigest(),flush=True)
    log=stem.with_suffix('.log')
    with log.open('w') as out:st=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(fn),str(pr)],stdout=out).returncode
    if st==20:
        with stem.with_suffix('.check').open('wb') as out:subprocess.run(['target/drat-trim/drat-trim',str(fn),str(pr)],stdout=out,check=True)
        assert b's VERIFIED' in stem.with_suffix('.check').read_bytes()
        print('all eight frames and 130 sites: s VERIFIED')
    elif st==10:
        model={int(z) for l in log.read_text().splitlines() if l.startswith('v ') for z in l[2:].split()}
        rows=[''.join('#' if bit(i,j) in model else '.' for j in range(n)) for i in range(n)]
        stem.with_suffix('.marks').write_text('\n'.join(rows)+'\n')
        print('SAT',sum(r.count('#') for r in rows),'marks; isolate',[p for p,z in flags.items() if z in model],flush=True)
        if dual in (1,3,6,8):
            score=verify(rows);k=(n-2)//3;assert score[0]==score[-1]==3*k*k+7*k-(k-5)//7
            print('physical spanning tree',score)
    else:print('UNKNOWN')
if __name__=='__main__':run(*map(int,sys.argv[1:]))

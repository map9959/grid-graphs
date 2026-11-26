"""Separate horizontal three-row forest extensions of physical patch marginals."""
from collections import Counter, defaultdict
from functools import lru_cache
from fractions import Fraction as Q
from pathlib import Path
import json
from .patch_square import MASKS, SYM, trans, relaxation, lpterms, verify_upper, signature
from .square_current import DIR
import subprocess


def advance(bits, parts, col):
    # Column-major indexing. Keep connectivity through the whole prefix,
    # including paths which leave the final column and return to it.
    p=list(parts)+[3,4,5]
    def root(i):
        while i!=p[i]:i=p[i]
        return i
    for i,j,on in [(i,i+3,(bits|col)>>i&1) for i in range(3)]+[
        (3+i,4+i,(col>>i|col>>(i+1))&1) for i in range(2)]:
        if on:
            a,b=root(i),root(j)
            if a==b:return None
            p[b]=a
    roots=[root(i) for i in range(3,6)]
    return tuple(roots.index(x) for x in roots)


@lru_cache(None)
def layers(n):
    states={(0,0,(0,1,2))}
    allrows=[]
    for j in range(n):
        arcs=[]
        for s in sorted(states):
            a,b,part=s
            for c in range(8):
                # For j=0 start the actual graph at its first column.
                nxt=advance(0,(0,1,2),c) if j==0 else advance(b,part,c)
                if nxt is None:continue
                m=sum(((z>>r)&1)<<(3*r+h) for h,z in enumerate((a,b,c)) for r in range(3))
                assert j<2 or m in MASKS
                arcs.append((s,(b,c,nxt),m))
        states={v for _,v,_ in arcs}
        allrows.append(arcs)
    return allrows


def model(n):
    names,rows,obj=relaxation(n)
    rows=list(rows)
    idx=len(names)
    for i in range((n-1)//2):
        incoming={}
        for j,arcs in enumerate(layers(n)):
            outgoing=defaultdict(Counter);new=defaultdict(Counter);probs=defaultdict(Counter)
            for s,t,m in arcs:
                x=f'x{idx}';idx+=1
                outgoing[s][x]=1;new[t][x]=1;probs[m][x]=1
            for s in outgoing:
                c=outgoing[s];c.subtract(incoming.get(s,{}))
                rows.append((tuple(c.items()),'=',int(j==0)))
            if j>=2:
                pos=[trans(i,j-2,n-2,g) for g in range(8)]
                for m in MASKS:
                    c=probs[m];c[names['p',min(zip(pos,SYM[m]))]]-=1
                    rows.append((tuple(c.items()),'=',0))
            incoming=new
    return rows,obj


def short_model(n):
    names,rows,obj=relaxation(n);rows=list(rows);seen=set()
    def var(i,j,m):
        return names['p',min((trans(i,j,n-2,g),SYM[m][g]) for g in range(8))]
    def cols(m):
        return tuple(sum((m>>(3*r+c)&1)<<r for r in range(3)) for c in range(3))
    words={cols(m):m for m in MASKS}
    for i in range(n-2):
        for j in range(n-3):
            for u,v in ((1,4),(4,1)):
                c=Counter([var(i,j,words[5,u,v]),var(i,j+1,words[u,v,5])])
                for w,m in words.items():
                    if w[1:]==(u,v):c[var(i,j,m)]-=1
                row=tuple(sorted((x,w) for x,w in c.items() if w))
                if row not in seen:rows.append((row,'<=',0));seen.add(row)
    return rows,obj


def solve(n,short=False,replay=False):
    rows,obj=(short_model if short else model)(n)
    path=Path(__file__).with_name(f'strip_forest_{n}_{"short" if short else "full"}.json')
    digest=signature(rows,obj)
    if replay:
        signed,ys=json.loads(path.read_text())
        assert signed==digest
        upper,err=verify_upper(rows,obj,{i:Q(y) for i,y in ys})
        print('solver-free upper',upper,'residual allowance',err)
        return
    text='max: '+lpterms(obj)+';\n'+''.join(
        f'r{i}: '+lpterms(dict(c))+f' {op} {b};\n' for i,(c,op,b) in enumerate(rows))
    print('strip LP side',n,'rows',len(rows),flush=True)
    p=subprocess.run(['lp_solve','-presolve','-S4'],input=text,text=True,capture_output=True,check=True)
    print(p.stdout.splitlines()[:3],flush=True)
    tail=p.stdout.split('Dual values with from - till limits:')[-1]
    ys={int(a[1:]):Q(b) for line in tail.splitlines() if len(line.split())==4
        for a,b,_,_ in [line.split()] if a.startswith('r') and a[1:].isdigit()}
    # Arc variables as well as all event probabilities are bounded by 1.
    upper,err=verify_upper(rows,obj,ys)
    print('exact rational upper and residual allowance',(upper,err),flush=True)
    k=n//3
    if n%3==1 and 3*k*k+5*k<=upper<3*k*k+5*k+1:
        path.write_text(json.dumps([digest,[[i,str(y)] for i,y in sorted(ys.items()) if y]],separators=(',',':'))+'\n')


def witness(n=13):
    """A deterministic pseudoforest admissible after D4 averaging in the old LP."""
    selected={(4+r,4+c) for c,z in enumerate((5,1,4,5)) for r in range(3) if z>>r&1}
    cycle=[(4,4+c) for c in range(4)]+[(5,7)]+[(6,7-c) for c in range(4)]+[(5,4)]
    out=dict(zip(cycle,cycle[1:]+cycle[:1]))
    for u in selected:
        for a,b in DIR:
            v=(u[0]+a,u[1]+b)
            if v not in cycle:
                assert v not in out or out[v]==u
                out[v]=u
    names,rows,obj=relaxation(n)
    freq=Counter()
    for S,kind in ((n,'s'),(n-2,'p')):
        for i in range(S):
            for j in range(S):
                pos=[trans(i,j,S,g) for g in range(8)]
                for g,p in enumerate(pos):
                    if kind=='p':
                        m=sum(1<<(3*r+c) for r in range(3) for c in range(3) if (i+r,j+c) in selected)
                        assert m in MASKS
                        key=(kind,min((pos[h],SYM[m][h]) for h in range(8)))
                    else:
                        f=int((i,j) in selected);words=[]
                        for h,ph in enumerate(pos):
                            nb=[9]*4;o=-1
                            for a,b in DIR:
                                u,v=i+a,j+b
                                if not(0<=u<n and 0<=v<n):continue
                                w=trans(u,v,n,h);d=DIR.index((w[0]-ph[0],w[1]-ph[1]))
                                nb[d]=int((u,v) in selected)
                                if out.get((i,j))==(u,v):o=d
                            words.append((ph,f,tuple(nb),o))
                        key=(kind,min(words))
                    freq[key]+=1
    # A variable is per individual labeled atom, not total orbit mass.
    orbit_sizes=Counter()
    for key in names:
        kind,atom=key;p=atom[0]
        if kind=='p':
            orbit_sizes[key]=len({(trans(*p,n-2,g),SYM[atom[1]][g]) for g in range(8)})
        else:
            _,f,nb,o=atom
            orbit_sizes[key]=len({(trans(*p,n,g),tuple(sorted((((2-d if g&4 else d)+g%4)%4,v)
                for d,v in enumerate(nb))),-1 if o<0 else ((2-o if g&4 else o)+g%4)%4) for g in range(8)})
    vals={x:Q(freq[key],8*orbit_sizes[key]) for key,x in names.items()}
    for c,op,b in rows:
        z=sum(w*vals[x] for x,w in c)
        assert z==b if op=='=' else z>=b
    assert sum(w*vals[x] for x,w in obj.items())==len(selected)
    print('old LP feasible: exact rows',len(rows),'selected',len(selected),'forced cycle length',len(cycle))
    cuts,_=short_model(n)
    violation=max(sum(w*vals[x] for x,w in c)-b for c,_,b in cuts[len(rows):])
    assert violation==Q(1,8)
    print('short-strip cut violation after symmetry averaging:',violation)


if __name__=='__main__':
    import sys
    if sys.argv[1]=='--witness':witness()
    else:solve(int(sys.argv[1]),'--short' in sys.argv,'--replay' in sys.argv)

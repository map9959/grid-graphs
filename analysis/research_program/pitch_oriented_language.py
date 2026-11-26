"""Match horizontal arrow directions as well as bits on a cap-window overlap."""
from collections import defaultdict
from functools import lru_cache
from itertools import product
from pathlib import Path
from .pitch_seam_language import dfa,image,contained

def directed(name,k,p,which,L=None,ranked=False,two=False):
    rows=Path('target/pitch_'+name+'.nfa').read_text().splitlines()
    ix=max(i for i,r in enumerate(rows) if r.startswith('NFA '))
    n=int(rows[ix].split()[1]);raw=[[] for _ in range(n)];F=set();sources=[]
    for row in rows[ix+1:]:
        v=row.split()
        if v[0]=='e':
            i,a,b,j,m=map(int,v[1:]);raw[i].append((j,m,a,b))
        if v[0]=='f':F.add(int(v[1]))
        if v[0]=='i':sources.append(tuple(map(int,v[1:])))
    w=3*k+2;mask=(1<<w)-1
    pitch=sum(1<<j for j in range(2,w-1,3))
    # Label every inter-triple horizontal bond in the retained overlap.
    left=tuple(3*j for j in range(p+1));right=tuple(i+3*(k-p) for i in left)
    def encode(bits,arrows,tape):
        return bits+((sum((arrows>>j&1)<<t for t,j in enumerate(tape)))<<(3*p+2))
    slits=set(right if which=='right' else left if which=='left' else left+right)
    @lru_cache(16384)
    def options(old,part,m):
        # Contract every unobserved forced edge. A resulting tree
        # needs at most one prescribed destination or outgoing slit.
        P=[v//2 for v in part]+list(range(w,2*w));paid={v//2 for v in part if v%2}
        def root(j):
            while P[j]!=j:j=P[j]
            return j
        def merge(j,k):
            a,b=root(j),root(k)
            if a==b:return True
            if a in paid and b in paid:return False
            P[a]=b
            if a in paid:paid.add(b)
            return True
        for j in range(w):
            if (old|m)>>j&1 and not merge(j,w+j):return ()
            if j and j-1 not in slits and m>>(j-1)&3 and not merge(w+j-1,w+j):return ()
        rs=[root(w+j) for j in range(w)];ids={x:rs.index(x) for x in set(rs)}
        base=tuple(ids[r]*2 for r in rs);used=sum(1<<ids[r] for r in ids if r in paid)
        ways=[(used,0)]
        for j in slits:
            if not m>>j&3:continue
            ways=[(s|1<<a,z|(arrow<<j)) for s,z in ways for a,arrow in
                  ((ids[rs[j]],1),(ids[rs[j+1]],0)) if not s>>a&1]
        return tuple((tuple(v+(u>>(v//2)&1) for v in base),z) for u,z in ways)
    def start(drop):return tuple(2*(0 if j==0 else w-1 if j==w-1 else 1+3*((j-1)//3))+
                int(j not in (0,w-1) and not drop>>((j-1)//3)&1) for j in range(w))
    st=[];lookup={};out=[];accept=set();head=defaultdict(set)
    if ranked:
        st.append(None)
        for t,drop in sources:
            a=-1-(drop&((1<<p)-1));b=-1-(drop>>(k-p))
            if L is not None and a not in L[0][0]:continue
            s=t,pitch,start(drop),0 if L is None else L[0][0][a]
            lookup[s]=len(st);st.append(s);j=lookup[s]
            if which=='right' or L is not None:head[b].add(j)
            elif which=='left':head[a].add((0,j))
            else:head[a].add((b,j))
    elif two:st.append((0,0,tuple(2*j for j in range(w)),0));lookup[st[0]]=0
    else:st.append((0,pitch,start(0),0));lookup[st[0]]=0
    allowed=None
    if L is not None:allowed=[{a% (1<<(3*p+2)) for a in row} for row in L[0]]
    for i,s in enumerate(st):
        if s is None:out.append(head);continue
        q,m,part,l=s
        if q in F and (L is None or l in L[1]) and all(not(m>>j&1 and part[j]%2) for j in range(w)):accept.add(i)
        tab=defaultdict(set)
        for t,v,a,b in raw[q]:
            if v>>63:
                assert two
                u=-999
                if L is not None and u not in L[0][l]:continue
                x=t,m,part,0 if L is None else L[0][l][u]
                if x not in lookup:lookup[x]=len(st);st.append(x)
                j=lookup[x]
                if which=='right' or L is not None:tab[u].add(j)
                else:tab[u].add((0 if which=='left' else u,j))
                continue
            if allowed is not None and a not in allowed[l]:continue
            for new,arrows in options(m,part,v):
                u=encode(a,arrows,left);z=encode(b,arrows,right)
                if L is not None and u not in L[0][l]:continue
                x=t,v,new,0 if L is None else L[0][l][u]
                if x not in lookup:lookup[x]=len(st);st.append(x)
                j=lookup[x]
                if which=='right' or L is not None:tab[z].add(j)
                elif which=='left':tab[u].add((0,j))
                else:tab[u].add((z,j))
        out.append(tab)
    print('oriented',name,len(st),'states',flush=True)
    return (dfa(out,accept) if which=='right' or L is not None else (out,accept))

def test(start=3,step=7,p=2,ranked=False,two=False):
    L=directed('start',start,p,'right',ranked=ranked,two=two);B=directed('stop',step,p,'left',ranked=ranked,two=two)
    T=None;old=[]
    for i in range(10):
        word=image(L,B,True);print(i,len(L[0]),'stop word',word,flush=True)
        if word is not None:return False
        if any(contained(L,r) for r in old):return True
        old.append(L);L=directed('step',step,p,'both',L,ranked,two)
    return False
if __name__=='__main__':
    import sys
    print('closed?',test(*map(int,sys.argv[1:])))

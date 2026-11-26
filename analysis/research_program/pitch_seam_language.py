"""Follow the vertical overlap words at a possible first negative-drift block."""
from collections import defaultdict,deque
from pathlib import Path

def load(name):
    rows=Path('target/pitch_'+name+'.nfa').read_text().splitlines();last=max(i for i,r in enumerate(rows) if r.startswith('NFA '))
    n=int(rows[last].split()[1]);tab=[defaultdict(list) for _ in range(n)];end=set()
    for row in rows[last+1:]:
        tag,*v=row.split();v=list(map(int,v))
        if tag=='e':i,a,b,j=v[:4];tab[i][a].append((b,j))
        if tag=='f':end.add(v[0])
    return tab,end

def dfa(graph,end):
    states=[frozenset({0})];ix={states[0]:0};out=[];accept=set()
    for i,s in enumerate(states):
        row=defaultdict(set)
        if s&end:accept.add(i)
        for u in s:
            for a,vs in graph[u].items():row[a].update(vs)
        z={}
        for a,vs in row.items():
            t=frozenset(vs)
            if t not in ix:ix[t]=len(states);states.append(t)
            z[a]=ix[t]
        out.append(z)
    # Drop states which cannot terminate, including useless symbols.
    pred=defaultdict(set)
    for i,row in enumerate(out):
        for j in row.values():pred[j].add(i)
    live=set(accept);q=list(live)
    for j in q:
        for i in pred[j]-live:live.add(i);q.append(i)
    colors={i:int(i in accept) for i in live}
    while True:
        keys={};c={}
        for i in sorted(live):
            k=i in accept,tuple(sorted((a,colors[j]) for a,j in out[i].items() if j in live))
            c[i]=keys.setdefault(k,len(keys))
        if c==colors:break
        colors=c
    if not live:return [{}],set()
    assert c[0]==0
    g=[{} for _ in keys]
    for i in live:g[c[i]]={a:c[j] for a,j in out[i].items() if j in live}
    return g,{c[i] for i in accept}

def image(L,T,stop=False):
    A,F=L;B,G=T
    states=[(0,0)];ix={states[0]:0};out=[];end=set();pred={}
    for k,(i,j) in enumerate(states):
        if i in F and j in G:
            if stop:
                word=[]
                while k: k,a=pred[k];word.append(a)
                return word[::-1]
            end.add(k)
        row=defaultdict(set)
        for a,u in A[i].items():
            for b,v in B[j].get(a,()):
                t=u,v
                if t not in ix:
                    ix[t]=len(states);pred[ix[t]]=k,a;states.append(t)
                row[b].add(ix[t])
        out.append(row)
    if stop:return None
    return dfa(out,end)

def contained(L,R):
    a,f=L;b,g=R;q=[(0,0)];seen=set(q)
    for i,j in q:
        if i in f and j not in g:return False
        for x,v in a[i].items():
            t=v,b[j].get(x,-1) if j>=0 else -1
            if t not in seen:seen.add(t);q.append(t)
    return True

def check():
    s,f=load('start');T=load('step');B=load('stop')
    graph=[defaultdict(set) for _ in s]
    for i,row in enumerate(s):
        for arcs in row.values():
            for b,j in arcs:graph[i][b].add(j)
    L=dfa(graph,f);old=[]
    for j in range(12):
        w=image(L,B,True)
        print('neutral blocks',j,'seam states',len(L[0]),'possible stop word',w,flush=True)
        if w is not None:return False
        if any(contained(L,r) for r in old):return True
        old.append(L);L=image(L,T)
    return False

if __name__=='__main__':print('language excludes negative drift?',check())

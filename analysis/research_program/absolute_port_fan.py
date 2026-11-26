"""Test a concrete north-isolate fan with every seam pinned to physical rows."""
import sys
from .absolute_ports import Words,column,symbols
from .ordered_ports import cols

def candidate(k,q,start):
    top=[16]+[48]*(q-2)+[16,4]+[6]*(k-q-1)
    bot=[192]*(k-2)+[128,8]
    assert len(top)==len(bot)==k
    cuts=[()];costs=[]
    for i in range(k):
        j=i-q
        if j < -5:pts=[]
        elif j==-5:pts=[(0,3),(3,3)]
        elif j==-4:pts=[(0,2),(7,3),(10,3)]
        elif j==-3:pts=[(4,2),(7,2),(14,3),(17,3)]
        elif j==-2:pts=[(11,2),(14,2),(21,3),(24,3)]
        elif j==-1:pts=[(18,2),(21,2),(28,3)]
        else:pts=[(25+4*j,2),(32+4*j,3)]
        if i==k-2:pts=pts[:1]
        if i==k-1:pts=[]
        cuts.append(tuple((start+y,t) for y,t in pts))
        costs.append(4 if i==k-1 else 3 if j<=-5 else 7 if j in (-4,0) else 9 if j<0 else 6)
    syms=[]
    for i,pts in enumerate(cuts):
        s=[0]*k
        for y,t in pts:
            assert 0<=y<3*k
            s[y//3]|=t<<(2*(y%3))
        if 0<i<k:
            s[0]|=(top[i-1]+512*top[i])<<6
            s[-1]|=(bot[i-1]+512*bot[i])<<6
        syms.append(tuple(s))
    return syms,costs

def unit(sym,parts):
    src=Words();u=src.leaf(dict.fromkeys(parts,1))
    for a in reversed(sym):u=src.node({a:u})
    return src,u

def solve(axis,k,q,start,verbose=True):
    sys.setrecursionlimit(5000)
    cuts,costs=candidate(k,q,start);parts={()};hist=[]
    for i,c in enumerate(costs):
        r=i if i<7 else 38-(k-1-i) if k-1-i<7 else 7
        d=max(-4,min(5,q-i));src,u=unit(cuts[i],parts);dst=Words()
        v=column(src,u,dst,axis,r,d,k,4,c,observed=cuts[i+1])
        for a in cuts[i+1]:
            if not v:break
            v=dst.nodes[v][a]
        hist.append((parts,r,d))
        parts={p for p,b in dst.nodes[v].items() if b>>c&1}
        if not parts:
            if verbose:print('axis',axis,'candidate fails at column',i,'offset',d,flush=True)
            return
        dst.merge.cache_clear()
    assert parts=={()}
    # Extract mutually compatible component partitions, not independent
    # column minima. Return all three masks of each actual tile witness.
    part=();witness=[]
    for i in reversed(range(k)):
        ps,r,d=hist[i];c=costs[i];src,u=unit(cuts[i],ps)
        rows,part,rem=column(src,u,None,axis,r,d,k,4,c,query=(cuts[i+1],part,c))
        assert rem==0
        witness.append(rows)
    assert part==()
    return witness[::-1]

def check(path,axis,q,start):
    k=len(path);cuts,costs=candidate(k,q,start)
    previous=[];peak=mismatch=0
    for i,rows in enumerate(path):
        sides=[[],[]]
        for j,w in enumerate(rows):
            for b,m in enumerate(cols(w)):
                for side,x in enumerate((3,6)):
                    marks=[(m>>u)&1 for u in range(x-2,x+2)]
                    a,l,r,z=marks
                    if l and r:h=1
                    elif a and not l and r:h=2
                    elif l and not r and z:h=3
                    else:continue
                    sides[side].append((3*j+b,h))
            assert symbols(i if i<7 else 38-(k-1-i) if k-1-i<7 else 7,w,j in (0,k-1))==(cuts[i][j],cuts[i+1][j])
        assert previous==sides[0] and len(sides[1])<=4
        previous=sides[1];peak=max(peak,len(previous))
        assert sum(3-w[1].bit_count() for w in rows)==costs[i]
        if i:mismatch+=sum(a[1:]!=b[:2] for a,b in zip(path[i-1],rows))
    assert not previous
    print('axis',axis,'k',k,'q',q,'first hop row',start,'peak',peak,'matched seams',k-1,
          'deficit',sum(costs),'overlap mask-pair disagreements',mismatch,flush=True)
    forest_replay(path,cuts)

def forest_replay(path,cuts):
    """Independent center-mark graph plus exactly the matched crossing edges."""
    k=len(path);N=3*k;marks=set()
    for i,col in enumerate(path):
        for j,(_,m,_) in enumerate(col):
            marks.update((3*i+b//3)*N+3*j+b%3 for b in range(9) if m>>b&1)
    p={u:u for u in marks}
    def root(u):
        while p[u]!=u:p[u]=p[p[u]];u=p[u]
        return u
    def join(u,v):
        a,b=root(u),root(v)
        assert a!=b
        p[a]=b
    extra=[];diag=[];used=set()
    for u in marks:
        x,y=divmod(u,N)
        for dx,dy in ((1,0),(0,1)):
            for dist in (1,2):
                xx,yy=x+dx*dist,y+dy*dist;v=xx*N+yy
                if xx>=N or yy>=N or v not in marks:continue
                if x//3==xx//3:join(u,v)
                else:
                    c=1 if dist==1 else 2 if xx%3==0 else 3
                    if cuts[xx//3][y//3]>>(2*(y%3))&3==c:
                        used.add((xx//3,y));join(u,v)
                    else:extra.append((x,y,dist))
                break
        for dy in (-1,1):
            if x+1<N and 0<=y+dy<N and u+N+dy in marks:diag.append((x,y,dy))
    assert len(used)==sum(bool(s>>(2*b)&3) for w in cuts for s in w for b in range(3))
    teeth={}
    for u in marks:
        x,y=divmod(u,N);a=root(u)
        teeth[a]=teeth.get(a,0)+int(x in (1,N-2) or y in (1,N-2))
    assert set(teeth.values())=={1}
    print('abstract forest:',len(marks),'marks,',len(used),'matched hops,',len(teeth),'trees, one tooth each')
    print('physically superimposed centers:',len(extra),'extra axial hops;',len(diag),
          'diagonal mark pairs; first examples',min(extra,default=None),min(diag,default=None))

def whole_masks(axis,k,q,start,no_extra=False):
    """Same candidate rows, but glue both shared tiles on every seam row."""
    sys.setrecursionlimit(5000)
    cuts,_=candidate(k,q,start);src=Words();u=src.unit(k)
    for i in range(k):
        r=i if i<7 else 38-(k-1-i) if k-1-i<7 else 7;dst=Words()
        v=column(src,u,dst,axis,r,max(-4,min(5,q-i)),k,4,0,False,
                 observed=cuts[i+1],full_masks=not no_extra,no_extra=no_extra)
        if not v:
            print('no-extra-hop' if no_extra else 'full-mask','version of this fan: no prefix through column',i)
            return False
        src,roots=dst.collect({0:v});u=roots[0];dst.merge.cache_clear()
    return True
if __name__=='__main__':
    a,k,q,s=map(int,sys.argv[1:]);w=solve(a,k,q,s)
    if w:check(w,a,q,s)

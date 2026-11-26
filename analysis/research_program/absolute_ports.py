"""Fixed transverse height. A cut is a word of k symbols, one per tile row.

Each symbol gives three exact hop types (0 if absent) and, on each end
row, the shared pair of masks. Leaves carry prefix partitions and costs.
Nondeterministic columns are projected by union of reduced word DAGs.
"""
from functools import lru_cache
from .ordered_ports import charts,links,step,cols,lane,glue,words,typ

class Words:
    def __init__(self):
        self.nodes=[{}];self.ids={};self.leaves={}
    def node(self,edges):
        if not edges:return 0
        k=tuple(sorted(edges.items()))
        if k not in self.ids:self.ids[k]=len(self.nodes);self.nodes.append(dict(k))
        return self.ids[k]
    def leaf(self,data):
        if not data:return 0
        k=tuple(sorted(data.items()))
        if k not in self.leaves:self.leaves[k]=len(self.nodes);self.nodes.append(dict(k))
        return self.leaves[k]
    def unit(self,k):
        v=self.leaf({():1})
        for _ in range(k):v=self.node({0:v})
        return v
    def collect(self,roots):
        other=Words()
        @lru_cache(None)
        def copy(v):
            if not v:return 0
            n=self.nodes[v]
            if isinstance(next(iter(n)),tuple):return other.leaf(n)
            return other.node({a:copy(w) for a,w in n.items()})
        return other,{d:copy(v) for d,v in roots.items() if v}
    @lru_cache(maxsize=100000)
    def merge(self,u,v):
        if not u or u==v:return v
        if not v:return u
        a=self.nodes[u];b=self.nodes[v];c=a.copy()
        if isinstance(next(iter(a)),tuple):
            for s,x in b.items():c[s]=c.get(s,0)|x
            return self.leaf(c)
        for x,w in b.items():c[x]=self.merge(c.get(x,0),w)
        return self.node(c)

@lru_cache(None)
def tab(axis,r,j,d):
    K=38;deep=tuple(min(x,K-x)>=4 for x in (j,j+1))
    t=links(3,r,typ(j,K),deep,axis)
    if j>2:return t
    return {w:[y for y in ys if all((w[h],y[h],w[h+1],y[h+1]) in
            charts(typ(i,K),typ(j,K),d+r-i) for h,i in enumerate((r-1,r)) if 0<=i<K)]
            for w,ys in t.items()}

BASE=-1,tuple(range(10)),(0,)*9+(1,)
CORE=-1,(0,1,2),(0,0,0)

@lru_cache(None)
def events(w):
    e=[0,0];rows=[]
    for b,m in enumerate(cols(w)):
        c=m>>3&7;ends=[]
        for side,x in enumerate((3,6)):
            v=m>>(x-2)&15
            typ=1 if v&6==6 else 2 if v&7==5 else 3 if v&14==10 else 0
            if typ:
                e[side]|=typ<<(2*b)
                i=(1 if typ==2 else 2) if side else int(typ==3)
                assert c>>i&1
                ends.append((side,i))
        rows.append((c,tuple(ends)))
    return *e,tuple(rows)

@lru_cache(maxsize=100000)
def piece(w,f,l,r,done,end,chart,cap,reverse):
    for b,(m,ends) in enumerate(events(w)[2]):
        tags=[(m>>i&1)*(1+2*(end and b==1 or 3*chart+i in (1,115))) for i in range(3)]
        for side,i in ends:
            if reverse:side=1-side
            n=r if side else l
            if n==cap:return
            tags[i]|=4<<(cap*side+n)
            if side:r+=1
            else:l+=1
        f,ds=lane(f,m,tuple(tags))
        if 1 in ds:return
        done+=tuple(x for x in ds if x!=3)
    return f,l,r,tuple(sorted(done))

@lru_cache(None)
def symbols(r,w,end):
    a,b,_=events(w)
    if end:
        if r:a|=(w[0]+512*w[1])<<6
        if r<38:b|=(w[1]+512*w[2])<<6
    return a,b

@lru_cache(None)
def actual_hops(west,east):
    bits=0
    for j in range(3):
        a,l,r,z=tuple((m>>(j+3*h))&1 for m,h in ((west,0),(west,1),(east,0),(east,1)))
        c=1 if l and r else 2 if a and r and not l else 3 if l and z and not r else 0
        bits|=c<<(2*j)
    return bits

def column(src,root,dst,axis,r,d,k,cap,budget,prices=True,query=None,observed=None,reverse=False,full_masks=False,no_extra=False):
    """Map every admitted input word, without enumerating its spellings."""
    phase=4 if d==5 else -4 if d==-4 else None
    rim=7<=r<=31
    north=words(3,True,phase) if rim else None
    south=words(3,False) if rim else None
    @lru_cache(None)
    def visit(j,w,z,f,l,h,done,cost,u):
        end=j in (0,k-1)
        a,b=symbols(r,w,end)
        if reverse:a,b=b,a
        if observed is not None and b!=observed[j]:return 0
        if full_masks:
            a,b=symbols(r,w,True)
            if reverse:a,b=b,a
        if no_extra:
            assert not query and not full_masks
            v=0
            for key,node in src.nodes[u].items():
                if key&0xffffff!=a:continue
                h=(actual_hops(w[1]>>3,key>>24) if reverse else actual_hops(key>>24,w[1]))
                if (r==38 if reverse else r==0) or h==(a&63):
                    v=src.merge(v,node)
            if reverse and r>0:b|=(w[1]&63)<<24
            if not reverse and r<38:b|=(w[1]>>3)<<24
        else:v=src.nodes[u].get(a,0)
        if not v or query and b!=query[0][j]:return 0
        z=step(z,w,end,r)
        if z is None:return 0
        g=piece(w,f,l,h,done,end,r,cap,reverse)
        if g is None:return 0
        f,l,h,done=g
        if prices:
            loss=3-w[1].bit_count()
            assert loss>=0
            cost+=loss
        if j==k-1:
            if rim and w not in south or 2 in z[2]:return 0
            trees=done+tuple(x for x in f[2] if x&1 and x!=3)
            if 1 in trees:return 0
            data={}
            for p,bits in src.nodes[v].items():
                q=glue(l,h,trees,p,cap)
                if q is not None:
                    assert cost>=0
                    if query and q==query[1] and query[2]>=cost and bits>>(query[2]-cost)&1:
                        return ((w,),p,query[2]-cost)
                    bs=bits<<cost & ((1<<(budget+1))-1)
                    if bs:data[q]=data.get(q,0)|bs
            if query:return 0
            sub=dst.leaf(data)
        else:
            jj=j if j<7 else 38-(k-1-j) if k-1-j<7 else 7
            sub=0
            for y in tab(axis,r,jj,d).get(w,()):
                child=visit(j+1,y,z,f,l,h,done,cost,v)
                if query:
                    if child:return ((w,)+child[0],*child[1:])
                else:sub=dst.merge(sub,child)
            if query:return 0
        return dst.node({b:sub}) if sub else 0
    out=0
    for w in tab(axis,r,0,d):
        if not rim or w in north:
            child=visit(0,w,BASE,CORE,0,0,(),0,root)
            if query and child:return child
            if not query:out=dst.merge(out,child)
    visit.cache_clear()
    return out

def run(axis,k=207,cap=4,budget=1062,prices=True,isolate=None,history=None,reverse=False,
        no_extra=False,full_masks=False):
    import sys
    assert k>=39 and cap>=0 and axis in (1,2)
    assert isolate is None or 1<=isolate<=k-2
    sys.setrecursionlimit(5000)
    src=Words();u=src.unit(k);roots=dict.fromkeys(range(-4,0) if reverse else range(1,6),u)
    for i in (reversed(range(k)) if reverse else range(k)):
        if history is not None:history.append((src,roots))
        r=i if i<7 else 38-(k-1-i) if k-1-i<7 else 7
        dst=Words();nxt={}
        for d,root in roots.items():
            if isolate is not None and d!=min(5,max(-4,isolate-i)):continue
            if r>=32 and d>37-r:continue
            if i<7 and d<1-i:continue
            v=column(src,root,dst,axis,r,d,k,cap,budget,prices,reverse=reverse,
                     no_extra=no_extra,full_masks=full_masks)
            offsets=((4,5) if d==5 else (max(-4,d-1),)) if not reverse else (
                (-4,-3) if d==-4 else (min(5,d+1),))
            for e in offsets:
                nxt[e]=dst.merge(nxt.get(e,0),v)
        dst.merge.cache_clear()
        src,roots=dst.collect(nxt)
        if i<8 or i%10==9 or not roots or i==k-1:
            print('axis',axis,'column index',i,'offsets',len(roots),'word DAG nodes',len(src.nodes),flush=True)
        if not roots:return 0
    bits=0
    for u in roots.values():
        for _ in range(k):
            assert set(src.nodes[u])=={0}
            u=src.nodes[u][0]
        assert set(src.nodes[u])=={()}
        bits|=src.nodes[u][()]
    return bits
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser()
    p.add_argument('axis',type=int);p.add_argument('--tiles',type=int,default=207)
    p.add_argument('--cap',type=int,default=4);p.add_argument('--budget',type=int,default=1062)
    p.add_argument('--isolate',type=int)
    p.add_argument('--reverse',action='store_true')
    x=p.add_mutually_exclusive_group()
    x.add_argument('--no-extra',action='store_true');x.add_argument('--full-masks',action='store_true')
    p.add_argument('--support',action='store_true');a=p.parse_args()
    b=run(a.axis,a.tiles,a.cap,a.budget,not a.support,a.isolate,reverse=a.reverse,
          no_extra=a.no_extra,full_masks=a.full_masks)
    print('terminal mask',hex(b),'budget present',bool(b>>a.budget&1) if not a.support else 'not priced')

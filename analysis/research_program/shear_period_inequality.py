"""Period-free Euler account and a window bound for unrestricted triplet choices."""
from collections import defaultdict
from .triple_pocket import model


def ledger(lo,hi,p,coords):
    d,sites,debit=model(lo,hi,p,0)
    f={i for i,(s,r,c) in enumerate(sites) if (r,c) in coords.get(s,())}
    selected={sites[i] for i in f}
    # FF components in the variable sites; a component joining an immutable
    # FF rod is not a new rod. Full outer horizontal rings have Euler count 0.
    ff=0;fixed=0
    for s,r,c in selected:
        if s!='C':
            ff+=((s,r+1,c) in selected)+((s,r,(c+1)%(3*p)) in selected)
            fixed+=int(r==0 and c%3==(1 if s=='T' else 0))
        else:
            q=(s,r-3*(c%3==2),(c+1)%(3*p))
            ff+=((s,r+1,c) in selected)+(q in selected)
            for a,b in ((r-1,c),(r+1,c),(r-3*(c%3==2),c+1),(r+3*(c%3==0),c-1)):
                fixed+=int((a<lo and b%3==1) or (a>hi and b%3==0))
    R=len(f)-ff-fixed
    holes=6*p-sum(s!='C' and r==2 for s,r,c in selected)
    E=sum(not cs or bool(f.intersection(cs)) for u,v,w,cs in d["edges"])
    trees=d["n"]-E
    net=len(f)-debit
    assert 3*(8*p-net)==holes+R+trees-p,(p,net,holes,R,trees)
    return net,holes,R,trees


def window(lo=0,hi=2):
    """Relax to cycles tested in each consecutive pair of blocks only."""
    h=hi-lo+1
    cells=list(product(range(lo,hi+1),range(3)))
    ids={}
    def name(p):return ids.setdefault(p,len(ids))
    def rod(r,c):
        b=c//3
        for j in range(b-1,b+2):
            if abs(c-3*j-1)+max(0,r-3*j-lo+1)<=1:return ('A',j)
            if abs(c-3*j)+max(0,3*j+hi+1-r)<=1:return ('B',j)
        return (r,c)
    def fixed(r,c):
        return c%3==1 and r-3*(c//3)<lo or c%3==0 and r-3*(c//3)>hi
    arr=[]
    for j in range(2):
        ed=[]
        for r,c in cells:
            r+=3*j;c+=3*j
            ls=[]
            for a,b in ((r+1,c),(r-1,c),(r,c+1),(r,c-1)):
                if not fixed(a,b):
                    ls.append((tuple(sorted(((a,b),(r,c)))),name(rod(r,c)),name(rod(a,b))))
            ed.append(ls)
        arr.append(ed)
    x,y=name(('B',0)),name(('A',1))
    def component(edges):
        par=list(range(len(ids)))
        def root(a):
            while par[a]!=a:a=par[a]
            return a
        for _,a,b in edges:
            a,b=root(a),root(b)
            if a==b:return None
            par[a]=b
        return root(x)!=root(y)
    candidates=[]
    for j in range(2):
        opt={}
        for m in range(1<<len(cells)):
            # Canonical physical edge id, oriented by the physical ordering
            # (root labels alone would erroneously deduplicate parallel edges).
            ed={e[0]:e for i,l in enumerate(arr[j]) if m>>i&1 for e in l}
            if component(ed.values()) is not None:opt[m]=ed
        candidates.append(opt)
    valid=list(candidates[0])
    assert set(valid)==set(candidates[1])
    transitions=[]
    for i,a in enumerate(valid):
        for j,b in enumerate(valid):
            split=component((candidates[0][a]|candidates[1][b]).values())
            if split is not None:transitions.append((i,j,a.bit_count()-h,int(split)))
    return valid,transitions


def potential(n,edges,penalty,norm=2):
    """Max-plus iteration with a full-vector recurrence, integer weights."""
    d=[0]*n;past={}
    for t in range(300):
        v=max(d);key=tuple(x-v for x in d)
        if key in past:
            a,b=past[key];return v-b,t-a
        past[key]=t,v
        nd=[-100000]*n
        for i,j,g,s in edges:nd[j]=max(nd[j],d[i]+norm*g+penalty*s)
        d=nd
    raise RuntimeError("inconclusive")


if __name__=='__main__':
    from .triple_pocket import run
    for p in (2,3):
        res,sites=run(-3,5,p,8*p-1)
        coords=defaultdict(set)
        for i in res['selected']:
            s,r,c=sites[i];coords[s].add((r,c))
        print("period, net, boundary holes, new carriers, tree components:",
              p,*ledger(-3,5,p,coords))
    valid,edges=window()
    print("valid masks, ordered adjacent pairs:",len(valid),len(edges))
    for pen in (0,1,2):
        print("split weight",pen,"/2; shift/period in half units:",potential(len(valid),edges,pen))

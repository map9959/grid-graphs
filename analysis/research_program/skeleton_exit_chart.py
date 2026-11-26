"""Joint star-level rank and symmetric line-cut inequalities on the sector chart."""
from collections import Counter,defaultdict
from fractions import Fraction as Q
from itertools import product
from .patch_square import DIR,trans,relaxation


def events(i,j,f,nb,out):
    joint=not(i%3 or j%3)
    def sk(a,b):return not(a%3 and b%3)
    base={d for d,(dy,dx) in enumerate(DIR) if nb[d]!=9 and
          ((f and sk(i,j)) or (nb[d] and sk(i+dy,j+dx)))}
    old=joint or bool(base)
    sink=int(joint and out==-1)
    exit=int(old and out!=-1 and out not in base)
    badsink=int(old and not joint and out==-1)
    path2=0
    if bool(i%3)!=bool(j%3):
        toward=(2 if j%3==1 else 0) if j%3 else (3 if i%3==1 else 1)
        other=(toward+2)%4
        path2=nb[other]*(f+2*(1-f)*nb[toward])
    return int(f and not sk(i,j)),path2,sink,exit,badsink


def tree_stage(i,j,S,d,w):
    def ax(t):return t if t<d else 2*d+3+t-S if t>=S-d else d+(t-d)%3
    def cl(t):return max(-w,min(w,t))
    return min((ax(a),ax(b),cl(a-b),cl(a+b+1-S))
               for a in (i,S-1-i) for b in (j,S-4-j))


def arrow_stage(i,j,out,S,d,w):
    h=d+4;lim=w+5
    def ax(t):return t if t<h else 2*h+3+t-S if t>=S-h else h+(t-h)%3
    def cl(t):return max(-lim,min(lim,t))
    return min((ax(a),ax(b),cl(a-b),cl(a+b+1-S),((2-out if g&4 else out)+g)%4)
               for g in range(8) for a,b in [trans(i,j,S,g)])


def model(n,d,w,cap=None,cuts=True,edge_floor=False,lines=False,faces=False,isolate_cut=False,
          tree_data=None,arrow_data=None,allow_pitch=False):
    h=d+4;lim=w+5
    base=next(t for t in range(4*h+2*lim+6,100) if t%6==n%6)
    if base>n:
        assert n>=2*h+3 and cap is None and not cuts and not edge_floor
        base=n
    ns,rows,obj=relaxation(base,h,pooled=d,period=3,diagonal=w)
    def pos(i,j,S,t):
        H=h-t
        def ax(z):return z if z<H else 2*H+3+z-S if z>=S-H else H+(z-H)%3
        clip=lambda z:max(-lim,min(lim,z))
        return ax(i),ax(j),clip(i-j),clip(i+j+1-S)
    N=[Counter(pos(i,j,n-2*t,t) for i,j in product(range(n-2*t),repeat=2)) for t in range(2)]
    reps={pos(i,j,base,0):(i,j) for i,j in product(range(base),repeat=2)}
    assert set(reps)==set(N[0])
    inv={x:k for k,x in ns.items()};A=[];b=[];bounds={}
    for row,op,r in rows:
        if op=='=' and r:
            kind,atom=inv[row[0][0]];r=N[int(kind=='p')][atom[0]]
        A.append((row,op));b.append(r)
    state=[Counter() for _ in range(4)];lc=defaultdict(Counter);empty=Counter()
    teeth=defaultdict(Counter);diff=defaultdict(Counter);axial=Counter()
    arrows=defaultdict(Counter);symmetric=defaultdict(Counter);missing=defaultdict(Counter);marg=defaultdict(Counter)
    possible=defaultdict(Counter);headed=defaultdict(Counter)
    marks=defaultdict(Counter);square=defaultdict(Counter)
    def et(i,j,S):
        def ax(z):return z if z<d else 2*d+3+z-S if z>=S-d else d+(z-d)%3
        cl=lambda z:max(-w,min(w,z))
        return ax(i),ax(j),cl(i-j),cl(i+j+1-S)
    def roles(i,j,S):
        if i%3:return ()
        if j%3:return ((et(i,j-j%3,S),-1),)
        return tuple((et(i,j-(3 if t==2 else 0),S),t) for t in (0,2)
                     if 0<=j+(3 if t==0 else -3)<S)
    if edge_floor:
        assert cap==43 and n==103
        for i,j in product(range(n),repeat=2):
            assert roles(i,j,n)==roles(*reps[pos(i,j,n,0)],base)
    for (kind,atom),x in ns.items():
        if kind!='s':continue
        pt,f,nb,out=atom;i,j=reps[pt];imgs=set()
        for g in range(8):
            rot=lambda s:((2-s if g&4 else s)+g)%4
            v=[9]*4
            for s in range(4):v[rot(s)]=nb[s]
            u,z=trans(i,j,base,g)
            imgs.add((pos(u,z,base,0),tuple(v),rot(out) if out>=0 else -1))
        assert not f or obj[x]==len(imgs)
        ev=events(i,j,f,nb,out)
        if arrow_data is not None and not(i%3 or j%3) and out>=0:
            arrow_data[arrow_stage(i,j,out,base,d,w)][x]+=len(imgs)
        if ev[-1]:bounds[x]=0
        if not(i%3 or j%3) and 1 not in nb:empty[x]=len(imgs)
        if cap==43 and n==103 and not(i%3 or j%3) and 1 not in nb:
            # C=1, slack1=0 in every axis assignment. An empty-stub
            # junction must be marked and receive a realized path, and
            # assigning its axis to that path wastes its missing slot.
            bounds[x]=0
        if bool(i%3)!=bool(j%3):
            along=(0,2) if j%3 else (1,3)
            if (f or any(nb[t]==1 for t in along)) and out>=0 and out not in along:
                axial[x]=len(imgs)
        for c,z in zip(state,ev):
            if z:c[x]=z*len(imgs)
        for p,v,o in imgs:
            u,z=reps[p];charge=f or (9 not in (v[1],v[3]) and v[1]!=v[3])
            if tree_data is not None and u%3==0 and z%3 and ev[1]:
                tree_data[tree_stage(u,z-z%3,base,d,w)][x]+=ev[1]
            if charge:lc[p[0]][x]+=1
            if isolate_cut:
                yp=et(u,z,base)[0]
                if f:
                    marks[yp][x]+=1
                    if et(u,z,base)[1]==yp:square[yp][x]+=1
                else:
                    for t in (1,3):
                        dy=DIR[t][0]
                        if v[t]==0 and v[(t+2)%4]==1:
                            possible[et(u,z,base),t][x]+=1
                        # Current site is the blank head, one step from the
                        # cut in direction t. It needs another marked neighbor.
                        if v[(t+2)%4]==0 and 1 in v and 0<u-dy<base-1:
                            headed[et(u-dy,z,base),t][x]+=1
            if edge_floor:
                if lines and not(u%3 or z%3):
                    marg[p[0],p[1],(int(v[2]==1),f,int(v[0]==1))][x]+=1
                for tag,t in roles(u,z,base):
                    start=z-z%3 if t==-1 else z-(3 if t==2 else 0)
                    edge=tree_stage(u,start,base,d,w)
                    if t==-1:
                        path=ev[1]
                        arrows[tag][x]-=path;symmetric[edge][x]-=path;missing[tag][x]+=path
                    else:
                        arrows[tag][x]+=2*(o==t);symmetric[edge][x]+=2*(o==t)
                        missing[tag][x]+=2*(v[t]==0 and v[2-t]==1)
            if f:
                diff[p[0]][x]+=1 if z%3 else -1
                if u%3 and not z%3:teeth[p[0]][x]+=1
    F,path2,sink,ex=state
    m=(n+2)//3;k=m-1
    def add(c,op,r):
        A.append((list(c.items()),op));b.append(r)
    c=path2.copy()
    for tab in (sink,ex):
        for x,v in tab.items():c[x]+=2*v
    add(c,'=',2*m*m)
    cr=axial.copy();cr.subtract(ex);add(cr,'=',0)
    c=obj.copy();c.subtract(F);c.update(sink);c.update(ex)
    if not allow_pitch:add(c,'<=',n*m)
    # For a score above the comb not all junctions are isolated empty
    # stubs: without any stubs at all M<=m²+2k², below the comb here.
    c=obj.copy();c.subtract(F);c.update(ex);c.update(empty)
    assert m*m+2*k*k<=3*k*k+5*k+(3*k-13)//10
    if not allow_pitch:add(c,'<=',n*m-1)
    if cap is not None:add(F,'<=',cap)
    bands=Counter()
    for (a,_,__,___),cnt in N[0].items():bands[a]+=cnt
    credit=Counter()
    for a,terms in (() if allow_pitch else teeth.items()):
        x='complete'+str(a);ns['complete',a]=x
        row=terms.copy();row[x]-=1;add(row,'<=',(m-1)*(bands[a]//n))
        credit[x]=2
    if not allow_pitch:
        credit.subtract(ex);add(credit,'<=',0)
        for a,terms in diff.items():add(terms,'>=',(1-m)*(bands[a]//n))
    if edge_floor:
        mass=Counter(et(i,z,n) for i in range(0,n,3) for z in range(0,n-1,3))
        for tag in sorted(mass):
            add(Counter({x:v for x,v in arrows[tag].items() if v}),'=',0)
            add(+missing[tag],'<=',2*mass[tag])
        for row in symmetric.values():add(Counter({x:v for x,v in row.items() if v}),'=',0)
    if cuts:
        budget=3*k*k+5*k+(3*k-13)//10-(3*k*k+3*k-2)
        for a,c in lc.items():
            # For any above-comb input p_i(horizontal)+p_i(vertical)≥budget+1.
            assert bands[a]%n==0
            add(Counter({x:2*v for x,v in c.items()}),'>=',(budget+1)*(bands[a]//n))
        if isolate_cut:
            for key,U in possible.items():
                x=ns['paidHead',key]='h'+str(len(ns))
                for c in (U,headed[key]):
                    row=c.copy();row[x]-=1;add(row,'>=',0)
                marks[key[0][0]][x]+=1
            sizes=Counter(et(i,0,n)[0] for i in range(n))
            for y,mass in sizes.items():
                row=Counter({x:2*mass*v for x,v in marks[y].items()})
                for x,v in square[y].items():row[x]-=2*v
                add(row,'>=',budget*mass*mass)
    if lines:
        assert edge_floor
        from .skeleton_floor_words import add_lines
        add_lines(ns,A,b,marg,n,h)
    if faces:
        assert edge_floor
        from .skeleton_wired_faces import add_faces
        add_faces(ns,A,b,base,d,w,2)
    return ns,A,b,obj,bounds,state


def exact_basic(A,b,hint):
    """Reconstruct a basic feasible point on its numerical support; verify separately."""
    import heapq
    live={x for x,v in hint.items() if v>1e-8}
    eq=[];rhs=[];inc=defaultdict(set);heap=[];piv=[]
    for (terms,op),v in zip(A,b):
        if op!='=' and abs(sum(w*hint[x] for x,w in terms)-v)>1e-7:continue
        row={x:Q(w) for x,w in terms if x in live and w}
        if not row:assert v==0;continue
        i=len(eq);eq.append(row);rhs.append(Q(v))
        for x in row:inc[x].add(i)
        heapq.heappush(heap,(len(row),i))
    while heap:
        size,i=heapq.heappop(heap);row=eq[i]
        if len(row)!=size:continue
        x=min(row,key=lambda k:(len(inc[k]),k))
        w=row[x]
        for z in row:inc[z].remove(i)
        del row[x];row={z:t/w for z,t in row.items()};v=rhs[i]/w
        eq[i]={};piv.append((x,row,v))
        for j in inc.pop(x):
            a=eq[j];t=a.pop(x);rhs[j]-=t*v
            for z,u in row.items():
                if z not in a:inc[z].add(j)
                a[z]=a.get(z,0)-t*u
                if not a[z]:del a[z];inc[z].remove(j)
            if a:heapq.heappush(heap,(len(a),j))
            else:assert rhs[j]==0
    val={x:Q(float(hint[x])).limit_denominator(10**6) for x in live}
    for x,row,v in reversed(piv):val[x]=v-sum(w*val[y] for y,w in row.items())
    return val


def certificate(n,d,w,save,edges=False,lines=False,faces=False,isolate_cut=False):
    import json
    from pathlib import Path
    assert n==103
    ns,A,b,obj,bounds,state=model(n,d,w,43,edge_floor=edges,lines=lines,faces=faces,isolate_cut=isolate_cut)
    A.append((list(obj.items()),'='));b.append(3647)
    path=Path(__file__).with_name(f'skeleton_exit_{n}_{d}_{w}'+('_lines' if lines else '_edges' if edges else '')+('_faces' if faces else '')+('_cut' if isolate_cut else '')+'.json')
    if save:
        from .side28_score import solve
        _,_,hint=solve(A,b,{},ns,interior='cross',bounds=bounds)
        val=exact_basic(A,b,hint)
    else:val={x:Q(v) for x,v in json.loads(path.read_text()).items()}
    assert set(val)<=set(ns.values()) and min(val.values())>=0
    assert not any(val.get(x,0) for x in bounds)
    for (terms,op),rhs in zip(A,b):
        g=sum(v*val.get(x,0) for x,v in terms)-rhs
        assert {'=':g==0,'<=':g<=0,'>=':g>=0}[op]
    totals=[sum(v*val.get(x,0) for x,v in c.items()) for c in state]
    assert totals==[43,2448,1,0]
    if save:path.write_text(json.dumps({x:str(v) for x,v in val.items() if v},sort_keys=True,separators=(',',':'))+'\n')
    print('exact fractional score 3647; F=43, C=A=1, j=0;',len(A),'constraints;',
          sum(bool(v) for v in val.values()),'nonzero variables')


def physical_events(rows):
    from .skeleton_cross_rank import physical,graphs
    n=len(rows);adj=[[] for _ in range(n*n)]
    for u,v in graphs(rows):adj[u].append(v);adj[v].append(u)
    parent={}
    # Process all junction roots first. A component can receive only one.
    for root in [i*n+j for i,j in product(range(0,n,3),repeat=2)]+list(range(n*n)):
        if root in parent:continue
        parent[root]=-1;q=[root]
        for u in q:
            for v in adj[u]:
                if v==parent[u]:continue
                assert v not in parent;parent[v]=u;q.append(v)
    total=[0]*5
    for i,j in product(range(n),repeat=2):
        p=parent[i*n+j]
        out=-1 if p<0 else DIR.index((p//n-i,p%n-j))
        nb=[int(rows[i+a][j+b]=='#') if 0<=i+a<n and 0<=j+b<n else 9 for a,b in DIR]
        for h,z in enumerate(events(i,j,rows[i][j]=='#',nb,out)):total[h]+=z
    F,j,A,X=physical(rows);assert total==[F,2*(((n+2)//3)**2-j-A),A,j,0]
    return total


if __name__=='__main__':
    import sys
    if '--physical' in sys.argv:
        from .comb_cap_transfer import construct
        from .cross_minor_refill import refill
        rows=construct(103,4)
        for r in (rows,refill([('#' if i%3==1 else '.')*5+'.'+s[6:] for i,s in enumerate(rows)])[0]):
            print('site sums F, twice realized, A, j, forbidden sinks:',physical_events(r))
        sys.exit()
    d,w,n=map(int,sys.argv[1:4])
    if '--replay' in sys.argv or '--save' in sys.argv:
        certificate(n,d,w,'--save' in sys.argv,bool({'--edges','--lines','--faces'}&set(sys.argv)),
                    '--lines' in sys.argv,'--faces' in sys.argv,'--isolate-cut' in sys.argv);sys.exit()
    from .side28_score import solve
    ns,A,b,obj,bounds,state=model(n,d,w,int(sys.argv[4]) if len(sys.argv)>4 else None,
                                 edge_floor=bool({'--edges','--lines','--faces'}&set(sys.argv)),lines='--lines' in sys.argv,
                                 faces='--faces' in sys.argv,isolate_cut='--isolate-cut' in sys.argv)
    print('cols rows forbidden sinks',len(ns),len(A),len(bounds),flush=True)
    z,_,sol=solve(A,b,obj,ns,interior=True,bounds=bounds)
    print('fractional upper (numerical)',z,'F,twice edges,A,j',
          [sum(v*sol[x] for x,v in c.items()) for c in state],flush=True)

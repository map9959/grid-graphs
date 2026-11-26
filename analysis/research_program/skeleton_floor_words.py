"""A no-slack coarse junction line at the first no-pitch rank floor."""
from itertools import product
from collections import Counter,defaultdict

LETTERS=tuple(product(range(2),repeat=3))  # left owned midpoint, junction, right midpoint


def next_state(st,t):
    l,z,r=t;H=bool(l or r)
    mode,a,hit=st
    if a is not None:
        u,v,w=a;oldH=bool(u or w)
        real=(w or l) and (w or v) and (l or z)
        paid=int(oldH and not w)+int(H and not l)
        if paid and (real or paid==2):return
        if mode in ('pre','one','tail') and not v and not (hit or l):return
        if mode=='one' and H and (v or not(hit and l)):return
    if mode in ('p0','p1'):
        if H or mode=='p1' and not z:return
        new='p1' if not z else mode
    elif H:
        if mode=='tail':return
        new='on'
    else:
        new={'pre':'pre','on':'one','one':'tail','tail':'tail'}[mode]
    return new,t,(a[-1] if a and not H else 0)


def finish(st):
    m,a,h=st
    return m=='p1' or m in ('one','on','tail') and (m=='on' or a[1] or h)


def priced(st,t,last,no_pure=False,allow_zero=False):
    mode,a,hit=st;l,z,r=t[:3];signed=len(t)==4
    H=t[3] if signed else bool(l or r);cost=0
    if mode in ('p0','p1'):
        if H:return
        cost=int(mode=='p1' and not z)
        new='p1' if not z else mode
        if last and new!='p1':
            if allow_zero:pass
            elif signed and not no_pure:cost-=1
            else:return
    else:
        if a is not None:
            u,v,w=a[:3];oldH=a[3] if signed else bool(u or w)
            real=(w or l) and (w or v) and (l or z)
            missing=int(oldH and not w)+int(H and not l)
            cost+=max(0,missing-int(not real))
            cost+=int(not oldH and not v and not(hit or l))
            if mode=='gap' and H:cost+=int(not(not v and hit and l))
        new='on' if H else 'pre' if mode=='pre' else 'gap'
        if last:
            if new=='pre':return
            cost+=int(not H and not z and not(a and a[2]))
    return (new,t,(a[2] if a and not H else 0)),cost


def add_lines(ns,A,b,marg,n,h,exceptional=0,weighted=False,signed=False,no_pure=False,allow_zero=False,track=False,ban=False,row_labels=None):
    def ax(z):return z if z<h else 2*h+3+z-n if z>=n-h else h+(z-h)%3
    m=n//3+1;layers=[];states={('pre',None,0),('p0',None,0)}
    if exceptional and not weighted:states.add(('exc',None,0))
    if track:states={(*s,True) for s in states}
    debit=Counter()
    for t in range(m):
        arcs=[]
        for s in sorted(states):
            letters=((*a,H) for a in LETTERS for H in (0,1) if H or not(a[0] or a[2])) if signed else LETTERS
            for a in letters:
                if t==0 and a[0] or t==m-1 and a[2]:continue
                if weighted:
                    res=priced(s[:3],a,t==m-1,no_pure,allow_zero)
                    if res is not None:
                        u=res[0]
                        if track:
                            pure=s[3] and a[:3]==(0,1,0)
                            if ban and t==m-1 and pure:continue
                            u=(*u,pure)
                        arcs.append((s,u))
                    continue
                if s[0]=='exc':
                    arcs.append((s,('exc',a,0)));continue
                u=next_state(s,a)
                if u is not None and (t!=m-1 or finish(u)):arcs.append((s,u))
        states={u for s,u in arcs};layers.append(arcs)
    for y in (sorted({ax(z) for z in range(0,n,3)}) if row_labels is None else row_labels):
        mass=defaultdict(Counter);flow=defaultdict(Counter);seen=set()
        for t,arcs in enumerate(layers):
            p=ax(3*t);prev=None if not t else ax(3*t-3)
            for s,u in arcs:
                key=prev,p,s,u
                if key in seen:continue
                seen.add(key);x=ns['floorLine',y,key]='w'+str(len(ns))
                if weighted:
                    cost=priced(s[:3],u[1],t==m-1,no_pure,allow_zero)[1]
                    if cost:debit[x]+=cost
                if not t and s[0]=='exc':debit[x]+=1
                if t:flow[prev,s][x]-=1
                if t!=m-1:flow[p,u][x]+=1
                mass[p,u[1]][x]+=1
        for (p,a),cs in mass.items():
            if signed:
                for x in cs:cs[x]*=2
            cs.subtract(marg.get((y,p,a),{}))
        for (yy,p,a),c in marg.items():
            if yy==y and (p,a) not in mass:mass[p,a].subtract(c)
        for cs in [*mass.values(),*flow.values()]:
            A.append(([(x,v) for x,v in cs.items() if v],'='));b.append(0)
    if exceptional or weighted:A.append((list(debit.items()),'<='));b.append(exceptional)

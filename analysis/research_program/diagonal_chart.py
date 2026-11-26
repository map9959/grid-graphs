"""Test a type chart that distinguishes diagonal sectors as well as edge distances."""
from .patch_square import relaxation,Counter
from .side28_score import solve
from .repeating_patch_dual import verify,recover,Q,Path,json
from .chart_counts import count
import sys

def run(n0,n,d,w):
    assert n>=n0 and (n-n0)%6==0
    rooted='shared' if '--nw-shared' in sys.argv else '--nw' in sys.argv
    assert not rooted or not any(z in sys.argv for z in ('--four','--directed','--seams')) and not any(z.startswith('--tracks=') for z in sys.argv)
    phase=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--phase=')),None)
    scope=next((s.split('=')[1] for s in sys.argv if s.startswith('--phase-scope=')),'all')
    arms=next((s.split('=')[1] for s in sys.argv if s.startswith('--arms=')),'0123')
    tol=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--phase-tol=')),0)
    group=None
    if phase is not None:
        from .patch_square import trans
        group=tuple(g for g in range(8) if all((trans(i,j,7,g)[0]%3==phase)==(i%3==phase) for i in range(7) for j in range(7)))
        ac={trans(0,0,7,int(q)) for q in arms}
        group=tuple(g for g in group if {trans(*p,7,g) for p in ac}==ac)
        assert not rooted and '--mark-tree' not in sys.argv
    frame=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--frame=')),None)
    if frame is not None:
        from .patch_square import trans
        assert not rooted and 0<=frame<16
        pins={}
        for q in range(4):
            for pair,value in (((0,0),1),((0,1),frame>>q&1),((1,0),1-(frame>>q&1))):
                pins[trans(*pair,n0,q)]=value
        group=tuple(g for g in (range(8) if group is None else group) if all(pins[trans(*p,n0,g)]==v for p,v in pins.items()))
    barpair='--opposite-bars' in sys.argv
    normals=next((tuple(map(int,s.split('=')[1].split(','))) for s in sys.argv if s.startswith('--normal-pair=')),None)
    if normals is not None:assert barpair and len(normals)==2
    if barpair:
        from .patch_square import trans
        assert group is None and not rooted and d>=6
        group=tuple(g for g in range(8) if trans(0,1,7,g)[0] in (0,6))
        if normals is not None:
            def high(i,j):return i%3==normals[int(j>0)]
            group=tuple(g for g in group if all(high(i,j)==high(*trans(i,j,n0,g)) for i in range(3) for j in (0,n0-1)))
    ns,rows,obj=relaxation(n0,d+4,pooled=d,period=3,diagonal=w,rooted=rooted,group_override=group)
    inv={x:k for k,x in ns.items()}
    seams='--seams' in sys.argv
    if seams:
        from .sector_fine_seams import lift as fines
        from itertools import chain
        more=fines(n0,ns,d,w);rows=chain(rows,((row,op,0) for row,op in more))
    tracks=next((z.split('=')[1] for z in sys.argv if z.startswith('--tracks=')),None)
    if tracks:
        from .diagonal_track_flow import lift as tracklift
        from itertools import chain
        R=tracklift(n0,ns,d,w,tuple(map(int,tracks.split(','))))
        rows=chain(rows,((row,op,0) for row,op in R))
    if '--four' in sys.argv:
        from .four_square import lift
        from itertools import chain
        rows=chain(rows,((row,op,0) for row,op in lift(n0,ns,d+3,3,d,w)))
    if '--directed' in sys.argv:
        from .directed_patch import lift as lift_directed
        from itertools import chain
        rows=chain(rows,((row,op,0) for row,op in lift_directed(n0,ns,d,w)))
    def counts(n):
        out=[]
        for patch in (False,True):
            S=n-2*patch;h=d+4-patch
            ax=lambda i:i if i<h else 2*h+3+i-S if i>=S-h else h+(i-h)%3
            cut=lambda z:max(-w-5,min(w+5,z))
            out.append(Counter((ax(i),ax(j),cut(i-j),cut(i+j+1-S)) for i in range(S) for j in range(S)))
        return out
    v=counts(n);base=counts(n0);plus=counts(n+6);twice=counts(n+12)
    assert all(a.keys()==b.keys() for a,b in zip(v,base)), 'type chart not yet saturated'
    A=[];b=[];diff=[]
    for row,op,r in rows:
        A.append((row,op));z=r;D=E=0
        if op=='=' and r>0:
            k,atom=inv[row[0][0]];p=int(k=='p');pos=atom[0]
            assert base[p][pos]==r
            z=v[p][pos];D=plus[p][pos]-z;E=twice[p][pos]-z-2*D
        b.append(z);diff.append((D,E))
    norm_limit=len(A)
    if barpair:
        h=d+4
        bad=[]
        for x,(kind,atom) in inv.items():
            if kind!='s':continue
            r,c,*_=atom[0]
            y=min(r,2*h+2-r);j=min(c,2*h+2-c)
            off=bool(not atom[1] and y in (0,3,6,9) and j>=10)
            if normals is not None and y>=10 and j<=9:
                absolute=r if r<h+3 else n0+r-2*h-3
                high=absolute%3==normals[int(c>=h+3)]
                must=329 if high else 1
                may=1021 if high else 73
                off|=bool((must if not atom[1] else ~may)>>j&1)
            if off:
                bad.append((x,1))
        A.append((bad,'='));b.append(0);diff.append((0,0))
    varying={}
    if '--owners' in sys.argv:
        from .sector_owner_flow import lift as ownerlift
        assert not rooted and group is None
        for cs,op,rhs in ownerlift(ns,n0,d,w):
            A.append((cs,op));b.append(rhs);diff.append((0,0))
    if '--seven-lines' in sys.argv:
        from .patch_square import trans
        assert d>=3 and not rooted and group is None
        # In a D4-averaged chart all four side expectations agree.
        # The minimum is represented by a common lower bound variable.
        profile='profile_min';ns[('minimum',0)]=profile
        pairs=[Counter({profile:1}) for _ in range(7)]
        hh=d+4;S=n0
        ax=lambda t:t if t<hh else 2*hh+3+t-S if t>=S-hh else hh+(t-hh)%3
        cl=lambda t:max(-w-5,min(w+5,t))
        loc=lambda i,j:(ax(i),ax(j),cl(i-j),cl(i+j+1-S))
        from .square_current import states,DIR
        for i in range(7):
            reps={loc(i,j):j for j in range(n0)}
            for j in reps.values():
                ps=[loc(*trans(i,j,S,g)) for g in range(8)]
                ds=tuple(s for s,(x,y) in enumerate(DIR) if 0<=i+x<S and 0<=j+y<S)
                for f,sg in states(ds):
                    if not f:continue
                    out=next((s for s,vv in sg.items() if vv[2]==(1 if s<2 else -1)),-1);opts=[]
                    for g in range(8):
                        rot=lambda x:((2-x if g&4 else x)+g)%4;nb=[9]*4
                        for s in ds:nb[rot(s)]=sg[s][int(s<2)]
                        opts.append((ps[g],f,tuple(nb),rot(out) if out>=0 else -1))
                    pairs[i][ns['s',min(opts)]]+=2 if j%3==0 else -1
        k=n//3
        for cs in pairs:
            v0=2*(k+1);varying[len(A)]=(v0,4,0)
            A.append((list(cs.items()),'<='));b.append(v0);diff.append((4,0))
        row=Counter(obj);row[profile]=-2
        v0=3*k*k+Q(53*k-13,10);varying[len(A)]=(v0,12*k+Q(113,5),24)
        A.append((list(row.items()),'<='));b.append(v0);diff.append(varying[len(A)-1][1:])
    if '--profile-cut' in sys.argv:
        from .patch_square import trans
        from .square_current import states,DIR
        assert d>=3 and not rooted
        gp=group or tuple(range(8));extra=[Counter(obj) for _ in range(8)]
        seen=set();height=d+4
        def sitept(i,j):
            ax=lambda u:u if u<height else 2*height+3+u-n0 if u>=n0-height else height+(u-height)%3
            cl=lambda u:max(-w-5,min(w+5,u))
            return ax(i),ax(j),cl(i-j),cl(i+j+1-n0)
        for i in range(n0):
            for j in range(n0):
                pts=[sitept(*trans(i,j,n0,g)) for g in range(8)]
                if pts[0] in seen:continue
                seen.add(pts[0]);weight=[]
                for g in range(8):
                    rr,cc=trans(i,j,n0,g)
                    weight.append((2 if cc%3==0 else -1) if rr in (2,n0-7) else 0)
                if not any(weight):continue
                ds=tuple(s for s,(a,c) in enumerate(DIR) if 0<=i+a<n0 and 0<=j+c<n0)
                for f,sg in states(ds):
                    if not f:continue
                    out=next((s for s,vv in sg.items() if vv[2]==(1 if s<2 else -1)),-1)
                    opts=[]
                    for g in gp:
                        rot=lambda x:((2-x if g&4 else x)+g)%4;nb=[9]*4
                        for s in ds:nb[rot(s)]=sg[s][int(s<2)]
                        opts.append((pts[g],f,tuple(nb),rot(out) if out>=0 else -1))
                    x=ns['s',min(opts)]
                    for q,coef in enumerate(weight):extra[q][x]+=coef
        k=n//3;rhs=3*k*k+Q(93*k+27,10)
        for cs in extra:
            varying[len(A)]=(rhs,12*k+Q(153,5),24)
            A.append((list(cs.items()),'<='));b.append(rhs);diff.append(varying[len(A)-1][1:])
    wrong='--central-wrong' in sys.argv
    if wrong:
        assert group is None and not rooted
        from .patch_square import trans,MASKS,SYM
        S=n0-2;h=d+3
        ax=lambda z:z if z<h else 2*h+3+z-S if z>=S-h else h+(z-h)%3
        cl=lambda z:max(-w-5,min(w+5,z))
        row=Counter()
        for i in range(S//2-2,S//2+3):
            for j in range(S//2-2,S//2+3):
                if max(abs(i-j),abs(i+j+1-S))>1:continue
                pts=[(ax(r),ax(c),cl(r-c),cl(r+c+1-S)) for g in range(8) for r,c in [trans(i,j,S,g)]]
                for m in (7,56,448,73,146,292):
                    if m not in (7<<(3*(-i%3)),73<<(-j%3)):row[ns['p',min(zip(pts,SYM[m]))]]+=1
        A.append((list(row.items()),'>='));b.append(1);diff.append((0,0))
    band=next((tuple(map(int,s.split('=')[1].split(','))) for s in sys.argv if s.startswith('--band-debits=')),None)
    if band:
        assert group is None and not rooted
        from .patch_square import trans,MASKS,SYM
        W,R=band;S=n0-2;h=d+3
        ax=lambda z:z if z<h else 2*h+3+z-S if z>=S-h else h+(z-h)%3
        cl=lambda z:max(-w-5,min(w+5,z))
        at=lambda i,j:(ax(i),ax(j),cl(i-j),cl(i+j+1-S))
        cells={at(i,j):(i,j) for i in range(h,S-h) for j in range(h,S-h) if min(abs(i-j),abs(i+j+1-S))<=W};row=Counter()
        for i,j in cells.values():
            pts=[at(*trans(i,j,S,g)) for g in range(8)]
            for mask in MASKS:
                if mask not in (7,56,448,73,146,292):row[ns['p',min(zip(pts,SYM[mask]))]]+=1
        A.append((list(row.items()),'>='));b.append(R);diff.append((0,0))
    defect=next((tuple(map(int,s.split('=')[1].split(','))) for s in sys.argv if s.startswith('--diag-defect=')),None)
    if defect is not None:
        assert group is None and not rooted
        from .patch_square import trans,MASKS,SYM
        S=n0-2;h=d+3
        ax=lambda z:z if z<h else 2*h+3+z-S if z>=S-h else h+(z-h)%3
        cl=lambda z:max(-w-5,min(w+5,z))
        def at(i,j):return ax(i),ax(j),cl(i-j),cl(i+j+1-S)
        cells={at(*trans(*defect,S,g)):trans(*defect,S,g) for g in range(8)}
        row=Counter()
        for i,j in cells.values():
            pts=[at(*trans(i,j,S,g)) for g in range(8)]
            for mask in MASKS:
                if mask not in (7,56,448,73,146,292):row[ns['p',min(zip(pts,SYM[mask]))]]+=1
        A.append((list(row.items()),'>='));b.append(1);diff.append((0,0))
    if frame is not None:
        from .patch_square import MASKS,SYM
        bad=set()
        for q in range(4):
            S=n0-2;h=d+3;i,j=trans(0,0,S,q)
            ax=lambda z:z if z<h else 2*h+3+z-S if z>=S-h else h+(z-h)%3
            cl=lambda z:max(-w-5,min(w+5,z))
            ps=[(ax(r),ax(c),cl(r-c),cl(r+c+1-S)) for g in range(8) for r,c in [trans(i,j,S,g)]]
            for m in MASKS:
                if any((m>>(3*(r-i)+c-j)&1)!=a for (r,c),a in pins.items() if i<=r<i+3 and j<=c<j+3):
                    bad.add(ns['p',min((ps[g],SYM[m][g]) for g in group)])
        A.append(([(x,1) for x in sorted(bad)],'='));b.append(0);diff.append((0,0))
    if phase is not None:
        assert d==4
        bad=[]
        arm_bits='--arm-bits' in sys.argv
        if arm_bits:
            from functools import lru_cache
            @lru_cache(None)
            def covered(pt):
                r,c,u,z=pt
                # lower bounds on actual physical row/column, and the
                # upper bound z on i+j+1-S in the NW half (clip -9).
                if abs(u)>5 or z>=w+5:return 0
                if r>=d+6 or c>=d+6:return 0
                h=d+3
                def origin(a,b):
                    return r+a>=h and c+b>=h and abs(u+a-b)<=1 and z+u+2*a<0 and z-u+2*b<0
                return sum(int(sum(origin(a,b) for a in range(x-2,x+1) for b in range(y-2,y+1))>=3)<<(3*x+y)
                           for x in range(3) for y in range(3))
            assert arms=='0' and group==(0,)
        for x,(kind,atom) in inv.items():
            if kind!='p':continue
            (r,c,u,z),mask=atom;h=d+3
            if arm_bits and (mask^(7<<(3*((phase-r)%3))))&covered(atom[0]):
                bad.append((x,1));continue
            if '--pure-only' in sys.argv and mask not in (7,56,448,73,146,292):continue
            if scope=='center' and max(abs(u),abs(z))>1:continue
            if scope=='flat' and max(abs(u),abs(z))<w+5:continue
            if scope=='quadrant' and arms=='0' and z+abs(u)>=0:continue
            if not (abs(u)<=1 and ('0' in arms and z<=0 or '2' in arms and z>=0)
                    or abs(z)<=1 and ('1' in arms and u<=0 or '3' in arms and u>=0)):continue
            if h<=r<h+3 and h<=c<h+3 and min(abs(u),abs(z))<=1 and mask!=7<<(3*((phase-r)%3)):bad.append((x,1))
        quota=next((int(s.split('=')[1]) for s in sys.argv if s.startswith('--arm-max=')),None)
        if quota is not None:
            assert arms=='0' and scope=='quadrant' and group==(0,)
            row=Counter();seen=set()
            from .patch_square import MASKS
            S=n0-2
            for i in range(h,(S-1+1)//2):
                for j in range(max(h,i-1),min(S//2,i+2)):
                    cl=lambda z:max(-w-5,min(w+5,z))
                    pt=(h+(i-h)%3,h+(j-h)%3,cl(i-j),cl(i+j+1-S))
                    if pt in seen:continue
                    seen.add(pt)
                    for m in MASKS:
                        if m not in (7,56,448,73,146,292):row[ns['p',(pt,m)]]+=1
            A.append((list(row.items()),'<='));b.append(quota);diff.append((0,0))
        if tol:
            from .patch_square import MASKS,SYM,trans
            S=n0-2;at=lambda i,j:(ax0(i),ax0(j),cl0(i-j),cl0(i+j+1-S))
            ax0=lambda x:x if x<h else 2*h+3+x-S if x>=S-h else h+(x-h)%3
            cl0=lambda x:max(-w-5,min(w+5,x))
            cells={at(i,j):(i,j) for i in range(h,S-h) for j in range(h,S-h) if min(abs(i-j),abs(i+j+1-S))<=1}
            badset={x for x,_ in bad};row=Counter()
            for i,j in cells.values():
                pts=[at(*trans(i,j,S,g)) for g in range(8)]
                for mask in MASKS:
                    x=ns['p',min((pts[g],SYM[mask][g]) for g in group)]
                    if x in badset:row[x]+=1
            A.append((list(row.items()),'<='));b.append(tol);diff.append((0,0))
        else:A.append((bad,'='));b.append(0);diff.append((0,0))
    tree='--mark-tree' in sys.argv
    gaps=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--rim-gaps=')),None)
    holes=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--rim-holes=')),None)
    if tree:
        from .patch_square import trans,DIR
        from itertools import product
        degree_row=Counter();seen=set()
        for i,j in product(range(n0),repeat=2):
            h=d+4;cl=lambda x:max(-w-5,min(w+5,x))
            ax=lambda x:x if x<h else 2*h+3+x-n0 if x>=n0-h else h+(x-h)%3
            points=[(ax(r),ax(c),cl(r-c),cl(r+c+1-n0)) for g in range(8) for r,c in [trans(i,j,n0,g)]]
            if points[0] in seen:continue
            seen.add(points[0])
            from .square_current import states
            ds=[s for s,(u,v) in enumerate(DIR) if 0<=i+u<n0 and 0<=j+v<n0]
            for f,sg in states(ds):
                out=next((s for s,v in sg.items() if v[2]==(1 if s<2 else -1)),-1)
                nb=[sg[s][int(s<2)] if s in ds else 9 for s in range(4)]
                opts=[]
                for g,pt in enumerate(points):
                    rot=lambda x:((2-x if g&4 else x)+g)%4
                    ls=[9]*4
                    for s in ds:ls[rot(s)]=nb[s]
                    opts.append((pt,f,tuple(ls),rot(out) if out>=0 else -1))
                x=ns['s',min(opts)]
                degree_row[x]+=2-nb.count(1) if f else -2*int(nb.count(1)==2)
        A.append((list(degree_row.items()),'='));b.append(2);diff.append((0,0))
    if gaps is not None:
        from .sector_rim_row import row as rimrow
        assert not rooted and group is None
        A.append((rimrow(ns,n0,d,w),'>='));b.append(2*gaps);diff.append((0,0))
    if holes is not None:
        from .sector_rim_row import row as rimrow
        assert not rooted and group is None
        A.append((rimrow(ns,n0,d,w,True),'>='));b.append(holes);diff.append((0,0))
    sink=next((s.split('=')[1] for s in sys.argv if s.startswith('--sinks=')),None)
    if sink:
        assert sink in ('marks','leaves','connected')
        bad=[]
        for x,(kind,atom) in inv.items():
            if kind!='s':continue
            pt,f,nb,out=atom
            if out!=-1 or nb.count(9)==2:continue
            degree=sum(a!=9 and (f or a) for a in nb)
            if degree and (sink=='connected' or (not f if sink=='marks' else degree!=1)):
                bad.append((x,1))
        A.append((bad,'='));b.append(0);diff.append((0,0))
    corners=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--corners=')),0)
    if corners:
        assert corners in (3,4) and not rooted
        from .patch_square import trans,MASKS,SYM
        S=n0-2;h=d+3
        ax=lambda z:z if z<h else 2*h+3+z-S if z>=S-h else h+(z-h)%3
        cl=lambda z:max(-w-5,min(w+5,z))
        pos=[(ax(i),ax(j),cl(i-j),cl(i+j+1-S)) for g in range(8) for i,j in [trans(0,0,S,g)]]
        for marked in (0,1):
            cs=Counter()
            for m in MASKS:
                if m&1==marked and (m>>1&1)+(m>>3&1)==1:
                    for q in range(4):
                        from .patch_square import transformed
                        rotated=transformed(m,q)
                        i,j=trans(0,0,S,q)
                        ps=[(ax(r),ax(c),cl(r-c),cl(r+c+1-S)) for g in range(8) for r,c in [trans(i,j,S,g)]]
                        cs[ns['p',min((ps[g],SYM[rotated][g]) for g in (group or range(8)))]]+=1
            A.append((list(cs.items()),'='));b.append(corners if marked else 4-corners);diff.append((0,0))
    print('chart',n0,n,d,w,'columns',len(ns),'rows',len(A),flush=True)
    path=Path(__file__).with_name(f'diagonal_d{d}_w{w}_{n0}'+('_four' if '--four' in sys.argv else '')+('_dir' if '--directed' in sys.argv else '')+('_track'+tracks if tracks else '')+('_seams' if seams else '')+'.json')
    if rooted:path=path.with_name(path.stem+('_nw_shared' if rooted=='shared' else '_nw')+'.json')
    if barpair:path=path.with_name(path.stem+'_oppositebars.json')
    if normals is not None:path=path.with_name(path.stem+'_normals'+''.join(map(str,normals))+'.json')
    if corners:path=path.with_name(path.stem+f'_corners{corners}.json')
    if sink:path=path.with_name(path.stem+'_'+sink+'.json')
    if tree:path=path.with_name(path.stem+'_marktree.json')
    if gaps is not None:path=path.with_name(path.stem+f'_rimgaps{gaps}.json')
    if holes is not None:path=path.with_name(path.stem+f'_rimholes{holes}.json')
    if '--owners' in sys.argv:path=path.with_name(path.stem+'_owners.json')
    if phase is not None:path=path.with_name(path.stem+f'_phase{phase}.json')
    if scope!='all':path=path.with_name(path.stem+f'_{scope}.json')
    if arms!='0123':path=path.with_name(path.stem+f'_arms{arms}.json')
    if phase is not None and quota is not None:path=path.with_name(path.stem+f'_max{quota}.json')
    if tol:path=path.with_name(path.stem+f'_tol{tol}.json')
    if '--pure-only' in sys.argv:path=path.with_name(path.stem+'_pure.json')
    if '--arm-bits' in sys.argv:path=path.with_name(path.stem+'_bits.json')
    if frame is not None:path=path.with_name(path.stem+f'_frame{frame}.json')
    if defect is not None:path=path.with_name(path.stem+f'_defect{defect[0]}_{defect[1]}.json')
    if band:path=path.with_name(path.stem+f'_band{band[0]}_{band[1]}.json')
    if '--profile-cut' in sys.argv:path=path.with_name(path.stem+'_profilecut.json')
    if '--seven-lines' in sys.argv:path=path.with_name(path.stem+'_sevenlines.json')
    if wrong:path=path.with_name(path.stem+'_centralwrong.json')
    if '--replay' in sys.argv:
        yc={int(i):Q(z) for i,z in json.loads(path.read_text()).items()}
    else:
        score,y,_=solve(A,b,obj,ns,interior='cross' if '--cross' in sys.argv else '--exact' not in sys.argv);k=(n-1)//3
        D,E=(sum(q*v[j] for q,v in zip(y,diff)) for j in (0,1))
        print('numerical excess over comb',score-3*k*k-5*k-(3*k-13)//10,
              'side +6 difference over 3k^2+6k',D-(12*k+24),'curvature excess',E-24,flush=True)
        if '--exact' not in sys.argv:return
        raw={i:Q(z) for i,z in enumerate(y) if abs(z)>1e-9}
        yc={i:z.limit_denominator(10**6) for i,z in raw.items()}
        if verify(A,obj,yc)>0:yc=recover(A,obj,raw)
    assert all(op=='=' or (yc.get(i,0)<=0 if op=='>=' else yc.get(i,0)>=0) for i,(row,op) in enumerate(A))
    assert verify(A,obj,yc)<=0
    for p in (0,1):
        S=n-2*p;tot=[0,0,0]
        for pt,amt in v[p].items():
            a,h,e=count(S,d+4-p,w+5,pt)
            assert a==amt
            for i,u in enumerate((a,h,e)):tot[i]+=u
        assert tot==[S*S,12*S+36,72],tot
    coeff=[0,0,0]
    for i,y in yc.items():
        row,op=A[i]
        if i<norm_limit and op=='=' and b[i]>0:
            k,atom=inv[row[0][0]];p=int(k=='p')
            vals=count(n-2*p,d+4-p,w+5,atom[0])
            assert vals==(b[i],*diff[i])
        else:vals=varying.get(i,(b[i],0,0))
        for j,x in enumerate(vals):coeff[j]+=y*x
    print('exact upper at',n,'Newton coefficients in steps of six:',*coeff,flush=True)
    if '--exact' in sys.argv:path.write_text(json.dumps({i:str(v) for i,v in yc.items() if v},separators=(',',':'))+'\n')
    return tuple(coeff)
if __name__=='__main__':run(*map(int,sys.argv[1:5]))

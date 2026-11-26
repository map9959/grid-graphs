"""Sew two independently oriented cap charts to the same square's patch measure."""
from collections import Counter,defaultdict
from functools import lru_cache
from itertools import product
from unittest.mock import patch
from .seam_rank_chart import model
from .patch_square import trans,SYM
from .rank44_faces import test,labels
from .side28_score import solve

N=103


@lru_cache(None)
def word(i,j,m,h,diag):
    def tag(y,z):
        clip=lambda x:max(-diag,min(diag,x))
        return (*labels(y,z,N-2,h),clip(y-z),clip(y+z+1-(N-2)))
    return min((tag(*trans(i,j,N-2,g)),a) for g,a in enumerate(SYM[m]))


def chart(cut,depth=1,diag=0):
    assert 2<=cut<=N-3
    ns,A,b,M,bo,F,sink,_=test(weighted=True,free=True,allow_pitch=True)
    def row(c,op,val):A.append(([(x,w) for x,w in c.items() if w],op));b.append(val)
    row(sink,'>=',1)
    def coordinates(h,w,t,dc,world):
        pos={}
        for i,j in product(range(h-2*t),range(w-2*t)):
            def ax(v,S):return v if v<dc else 2*dc+3+v-S if v>=S-dc else dc+(v-dc)%3
            tag=(ax(i,h-2*t),ax(j,w-2*t))
            if diag:
                clip=lambda x:max(-diag-5,min(diag+5,x));y=world(i,t)
                tag+=clip(y-j),clip(y+j+1-(N-2*t))
            pos[tag]=(i,j)
        return pos
    def fine(i,j,t):
        S=N-2*t
        return (*labels(i,j,S,8-t),max(-9,min(9,i-j)),max(-9,min(9,i+j+1-S)))
    reps=[{fine(i,j,t):(i,j) for i,j in product(range(N-2*t),repeat=2)} for t in (0,1)]
    laws=defaultdict(Counter);Hrim=Counter();pair=[defaultdict(Counter) for _ in range(2)]
    wgt=depth+1
    for key,x in ns.items():
        if key[0]=='p':
            p,m=key[1];i,j=reps[1][p]
            imgs={(fine(*trans(i,j,N-2,g),1),q) for g,q in enumerate(SYM[m])}
            laws[word(i,j,m,wgt,diag)][x]-=len(imgs)
        elif key[0]=='s':
            p,f,nb,o=key[1]
            if f or 9 not in nb:continue
            i,j=reps[0][p];imgs=set()
            for g in range(8):
                rot=lambda s:((2-s if g&4 else s)+g)%4
                v=[9]*4
                for s,a in enumerate(nb):v[rot(s)]=a
                imgs.add((fine(*trans(i,j,N,g),0),tuple(v),rot(o) if o>=0 else -1))
            Hrim[x]=len(imgs)
    row(Hrim,'<=',16) # choose a maximum with maximal rim occupancy
    totalj=Counter();both=Counter();caps=[];cuts=defaultdict(Counter)
    for side,h in enumerate((cut,N-1-cut)):
        height=h+1
        world=lambda i,t:cut+i if side else cut-i-2*t
        with patch('sys.argv',['cap','--free-top','--free-bottom','--unwired']+([f'--box-diag={diag}'] if diag else [])):
            ca,cb,_,cn,_=model(height,N,depth,world=world)
        rename={v:f'c{side}_{v}' for v in cn.values()}
        for k,x in cn.items():ns['cap',side,k]=rename[x]
        for (rr,op),rhs in zip(ca,cb):A.append(([(rename[x],v) for x,v in rr],op));b.append(rhs)
        del ca
        locs=[coordinates(height,N,t,depth+4-t,world) for t in (0,1)]
        J=Counter();marks=Counter();vac=Counter()
        possible=defaultdict(Counter);heads=defaultdict(Counter)
        for k0,z in cn.items():
            x=rename[z];kind,p,*data=k0;i,j=locs[int(kind=='p')][p]
            if kind=='p':
                m,=data
                if i==0 and m&7!=sum((int((j+s)%3==0)<<s) for s in range(3)):
                    bo[x]=0
                y=cut+i if side else cut-i-2
                laws[word(y,j,m if side else SYM[m][6],wgt,diag)][x]+=1
            else:
                f,nb,o=data
                if i==0:
                    if f!=int(j%3==0) or (f and o not in (-1,1)):bo[x]=0
                    if j%3==0:
                        waive=int(o==1)
                        if waive:J[x]=1
                        pair[side][(p[1],*p[2:]),nb[1],waive][x]+=1
                else:
                    if f:marks[x]=1
                    if j in (0,N-1) and not f and nb[3]==1:vac[x]=1
                    tag=lambda j:labels(0,j,N,depth+2)[1]
                    if f:cuts[tag(j)][x]+=1
                    else:
                        for u,dd in ((0,1),(2,-1)):
                            if 0<j<N-1 and nb[u]==0 and nb[2-u]==1:
                                possible[p[0],tag(j),u][x]+=1
                            if 0<j-dd<N-1 and nb[2-u]==0 and (1 in nb or i==1 and j%3==0):
                                heads[p[0],tag(j-dd),u][x]+=1
        for key,P in possible.items():
            x=ns['risky',side,key]='risk'+str(len(ns))
            for c in (P,heads[key]):c[x]-=1;row(c,'>=',0)
            cuts[key[1]][x]+=1
        cap=Counter({x:20*w for x,w in marks.items()})
        for x,w in J.items():cap[x]-=15*w
        for x,w in vac.items():cap[x]+=10*w
        row(cap,'<=',20*h*35+6*34)
        totalj.update(J);both.update(marks);caps.append((marks,J,vac))
    row(totalj,'<=',34)
    for t,num in Counter(labels(0,j,N,depth+2)[1] for j in range(N)).items():row(cuts[t],'>=',44*num)
    both.subtract(M);row(both,'=',-35)
    # Each tooth carries the two first-row mark bits AND the directions
    # of its two compulsory spokes. The root of each bipartite incidence
    # tree can be taken at an edge: no tooth departs into both caps.
    roles={}
    for j in range(0,N,3):
        p=(labels(0,j,N,depth+4)[1],)
        if diag:
            clip=lambda x:max(-diag-5,min(diag+5,x))
            p+=clip(cut-j),clip(cut+j+1-N)
        # Canonical weight computed below; save actual geometries.
        rs=tuple((k,j-k) for k in range(max(0,j-2),min(N-3,j)+1))
        for a,c in product((0,1),repeat=2):
            terms=tuple(word(cut-1,k,(a|8|(c<<6))<<off,wgt,diag) for k,off in rs)
            assert roles.setdefault((p,a,c),terms)==terms
    for p,a,c in roles:
        for u,v in ((0,0),(0,1),(1,0)):
            x=ns['sewn',p,a,c,u,v]='seam'+str(len(ns))
            pair[0][p,a,u][x]-=1;pair[1][p,c,v][x]-=1
            for tag in roles[p,a,c]:laws[tag][x]+=1
    for grp in pair:
        for rr in grp.values():row(rr,'=',0)
    for rr in laws.values():row(rr,'=',0)
    return ns,A,b,M,bo,caps


if __name__=='__main__':
    import sys
    ns,A,b,M,bo,caps=chart(*map(int,sys.argv[1:]))
    v,y,x=solve(A,b,M,ns,interior=True,bounds=bo)
    print('pitch cut',sys.argv[1],'LP upper',v,'marks/joins/vacancy-runs',
          [[sum(x[z]*w for z,w in c.items()) for c in cap] for cap in caps],flush=True)

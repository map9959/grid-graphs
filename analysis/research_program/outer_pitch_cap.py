"""Rectangle between the rim and the outermost aligned pitch cut."""
from collections import Counter,defaultdict
from itertools import product
from unittest.mock import patch
from .seam_rank_chart import model
from .rank44_faces import table,colors
from .four_square import masks4
from .patch_square import MASKS
from .skeleton_exit_chart import events
from .skeleton_floor_words import add_lines
from .side28_score import solve


def chart(h,n=103,depth=1):
    assert h%3==0 and h>=3
    H=h+1;nsites=(h//3+1)*(n//3+1)
    with patch('sys.argv',['cap','--free-top','--free-bottom','--unwired']):
        A,b,_,ns,_=model(H,n,depth)
    def push(c,op,v):A.append(([(x,w) for x,w in c.items() if w],op));b.append(v)
    def ax(x,size,d):return x if x<d else 2*d+3+x-size if x>=size-d else d+(x-d)%3
    def pt(i,j,t,d):return ax(i,H-2*t,d),ax(j,n-2*t,d)
    reps=[{pt(i,j,t,depth+4-t):(i,j) for i,j in product(range(H-2*t),range(n-2*t))} for t in (0,1)]
    mark=Counter();F=Counter();C=Counter();S=Counter();ex=Counter();path=Counter();J=Counter();vac=Counter();bo={}
    marg=[defaultdict(Counter),defaultdict(Counter)]
    for name,x in ns.items():
        typ,p,*data=name;i,j=reps[int(typ=='p')][p]
        if typ=='p':
            if i==0 and data[0]&7 != 1<<((-j)%3):bo[x]=0
            continue
        f,nb,o=data
        if i==0 and (f!=int(j%3==0) or f and o not in (-1,1)):bo[x]=0
        if i==0 and j%3==0 and o==1:J[x]=1
        if i and j in (0,n-1) and not f and nb[3]==1:vac[x]=1
        if f:mark[x]=1
        ff,t,s,e,bad=events(i,j,f,nb,o)
        if ff:F[x]=1
        if t:path[x]=t
        if s or e:C[x]=s+e
        if s:S[x]=s
        if e:ex[x]=1
        if bad:bo[x]=0
        if i%3 or j%3:continue
        for vert in (0,1):
            d=(3,1) if vert else (2,0);letter=(int(nb[d[0]]==1),f,int(nb[d[1]]==1))
            choices=(1,1) if letter[0] or letter[2] else (0,0) if 1 in nb else (0,1)
            for axis in choices:marg[vert][p[vert],p[1-vert],(*letter,axis)][x]+=1
    pp=path.copy()
    for x,v in C.items():pp[x]+=2*v
    push(pp,'=',2*nsites)
    # Each full-cap junction class missing the seam survives alone in
    # the whole board. At least one further class touches the seam.
    isolated=S.copy();isolated.update(J);push(isolated,'<=',n//3+1+4)
    # No symmetry in these cap measures. Use every actual four-corner
    # label relation, but forget the labels after accumulating face rank.
    # For each mark mask the least possible rank is safe and avoids
    # thousands of duplicate columns.
    rank={}
    for (m,q),v in table(4,3).items():rank[m]=min(v,rank.get(m,4))
    kids=defaultdict(set);orig=set();words=[defaultdict(Counter),defaultdict(Counter)]
    face=lambda i,j:(ax(i,H-3,1),ax(j,n-3,1))
    for i,j in product(range(0,H-3,3),range(0,n-3,3)):
        p=face(i,j);orig.add(p)
        for t,(a,z) in enumerate(product(range(2),repeat=2)):kids[p,t].add(pt(i+a,j+z,1,depth+3))
    paid=Counter()
    for p in sorted(orig):
        sub=defaultdict(Counter)
        for m,v in rank.items():
            x=ns['outerFace',p,m]='f'+str(len(ns))
            if v:paid[x]=v
            for t,z in enumerate(masks4()[m][0]):sub[t,z][x]+=1
            for a in (0,3):
                for vert in (0,1):
                    w=tuple(m>>(4*z+a if vert else 4*a+z)&1 for z in range(4))
                    words[vert][p,a,w][x]+=1
        for t,z in product(range(4),MASKS):
            c=sub[t,z]
            for q in kids[p,t]:c[ns['p',q,z]]-=1
            push(c,'=',0)
    paid.subtract(ex);push(paid,'<=',0)
    debit=Counter()
    for vert,wds in enumerate(words):
        l,w=(n,H) if vert else (H,n)
        for y in sorted({ax(i,l,depth+4) for i in range(0,l,3)}):
            # add_lines normally makes copies for all row labels of a
            # square. Filter its row label domain to this single label.
            names={};rows=[];rhs=[];marg1={k:c for k,c in marg[vert].items() if k[0]==y}
            add_lines(names,rows,rhs,marg1,w,depth+4,weighted=True,signed=True,track=True,
                      ban=not vert and y!=0,row_labels=(y,))
            rename={v:f'L{vert}_{y}_{v}' for v in names.values()}
            role={}
            for yy,j in product(range(0,l,3),range(0,w-1,3)):
                if ax(yy,l,depth+4)!=y:continue
                p,q=(ax(z,w,depth+4) for z in (j,j+3))
                tags=tuple((face(j,yy-a) if vert else face(yy-a,j),a)
                           for a in (0,3) if 0<=yy-a<l-3)
                assert role.setdefault((p,q),tags)==tags
            for key,v in names.items():
                _,_,(p,q,s,u)=key;x=rename[v];ns['outerLine',vert,key]=x
                if p is None:continue
                word=(*s[1][1:3],*u[1][:2])
                for tag,a in role[p,q]:wds[tag,a,word][x]-=1
            for idx,((rr,op),z) in enumerate(zip(rows,rhs)):
                c=Counter({rename.get(x,x):v for x,v in rr})
                if idx==len(rows)-1:debit.update(c)
                else:push(c,op,z)
        for c in wds.values():push(c,'=',0)
    debit.update(mark);debit.update(C);debit.subtract(F)
    push(debit,'=',3*nsites-(h//3+1)-(n//3+1))
    c=Counter({x:20*w for x,w in mark.items()})
    for x,w in J.items():c[x]-=15*w
    for x,w in vac.items():c[x]+=10*w
    push(c,'<=',20*H*(n//3+1)+6*(n//3))
    return ns,A,b,mark,J,bo


if __name__=='__main__':
    import sys
    h=int(sys.argv[1]);ns,A,b,M,J,bo=chart(h)
    score=Counter({x:10*v for x,v in M.items()})
    for x,v in J.items():score[x]-=7*v
    z,_,v=solve(A,b,score,ns,interior=True,bounds=bo)
    print('outer cap height',h,'10b-7j upper',z-350*(h+1),'fractional rank',sum(v[x] for x in J))

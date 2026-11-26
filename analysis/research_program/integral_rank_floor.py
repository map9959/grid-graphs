"""One integral floor forest: shared physical mask, both seam directions, all F refills."""
from itertools import combinations,product
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
from pysat.formula import CNF,IDPool
from .physical_mark_count import add as atleast
from .cross_minor_price import verify
from .skeleton_cross_rank import physical


class Floor:
    def __init__(self,n,F):
        self.n=n;self.f=f=CNF();self.p=p=IDPool()
        assert n>=4 and n%3==1
        self.X=X=[[p.id() for _ in range(n)] for _ in range(n)]
        self.false=p.id();f.append([-self.false]);self.O=O={};D=((0,1),(1,0),(0,-1),(-1,0))
        sheet=[[p.id() for _ in range(n)] for _ in range(n)]
        for i,j in product(range(n),repeat=2):
            dirs={s:p.id() for s,(a,b) in enumerate(D) if 0<=i+a<n and 0<=j+b<n}
            O[i,j]=dirs
            for a,b in combinations(dirs.values(),2):f.append([-a,-b])
            if (i,j)==(0,0):
                for a in dirs.values():f.append([-a])
        for i,j in product(range(n),repeat=2):
            for s,a in O[i,j].items():
                u,v=i+D[s][0],j+D[s][1];r=O[u,v][(s+2)%4]
                if s<2:
                    f.extend([[-a,-r],[-X[i][j],a,r],[-X[u][v],a,r],
                              [-a,X[i][j],X[u][v]],[-r,X[i][j],X[u][v]]])
                for t,b in O[u,v].items():
                    if t==(s+2)%4:continue
                    z=sheet[u][v]*(-1 if abs(s-t)==3 else 1);w=sheet[i][j]
                    f.extend([[-a,-b,-w,z],[-a,-b,w,-z]])
            if i%3==0 and j%3==0:
                if i or j:f.append(list(O[i,j].values()))
                # In the connected coarse tree a junction parent is
                # reached along *three* successive forced bonds.
                for s,a in O[i,j].items():
                    di,dj=D[s]
                    for t in (1,2):f.append([-a,O[i+t*di,j+t*dj][s]])
            if i+1<n and j+1<n:
                f.extend([[-X[i][j],-X[i+1][j+1]],[-X[i+1][j],-X[i][j+1]]])
        lines=X+list(map(list,zip(*X)))
        for i,row in enumerate(lines):
            # Nonjunction lines could only contain all teeth by making
            # another join, or by being pitch.
            if (i%n)%3:f.append([-x for x in row[::3]])
            else:self.line(row)
        for i,j in product(range(0,n,3),repeat=2):
            f.append([X[i+D[s][0]][j+D[s][1]] for s in O[i,j]])
        off=[X[i][j] for i,j in product(range(n),repeat=2) if i%3 and j%3]
        # Floor words give M=n*(k+1)+F-1. For 103, F>=43 suffices:
        # the independent unrestricted upper then forces equality.
        if F:atleast(f,p,off,F)
        if n==103 and F==43:
            from pysat.card import CardEnc,EncType
            f.extend(CardEnc.atmost(off,43,vpool=p,encoding=EncType.cardnetwrk).clauses)
            self.bend_budget()
            self.score_budget()

    def disj(self,lits):
        z=self.p.id()
        self.f.append([-z,*lits])
        for x in lits:self.f.append([-x,z])
        return z

    def conj(self,lits):
        return -self.disj([-x for x in lits])

    def bend_budget(self):
        """For 3647 marks there are at most 73 straight blank joins available."""
        from pysat.card import CardEnc,EncType
        n=self.n;D=((0,1),(1,0),(0,-1),(-1,0));ed={}
        for i,j in product(range(0,n,3),repeat=2):
            for d in (0,1):
                di,dj=D[d];y,x=i+3*di,j+3*dj
                if max(y,x)>=n:continue
                e=self.disj([self.O[i,j][d],self.O[y,x][d+2]])
                ed[i,j,d]=ed[y,x,d+2]=e
                z,s,t,Z=(self.X[i+h*di][j+h*dj] for h in range(4))
                self.f.extend([[e,-s,-t],[e,-s,-Z],[e,-z,-t]])
        cost=[];self.mixed={}
        for i,j in product(range(0,n,3),repeat=2):
            a,b,c,d=[ed.get((i,j,t),self.false) for t in range(4)]
            self.mixed[i,j]=self.conj([self.disj([a,c]),self.disj([b,d])])
            cost.append(self.mixed[i,j])
            if min(i,j,n-1-i,n-1-j)>0:cost.append(self.conj([a,b,c,d]))
        self.ed=ed
        for i,j in product(range(0,n,3),repeat=2):
            for t,u in ((0,2),(1,3)):
                if (i,j,t) in ed and (i,j,u) in ed:
                    # If both axial edges are realized, both owned
                    # slots must be marked (the V-gap rule would instead
                    # force a vacant junction if neither were).
                    for d in (t,u):
                        a,b=D[d]
                        self.f.append([-ed[i,j,t],-ed[i,j,u],self.X[i+a][j+b]])
        # The rational incident-profile dual certificates tighten 0..73.
        self.f.extend(CardEnc.atmost(cost,72,vpool=self.p,encoding=EncType.cardnetwrk).clauses)
        atleast(self.f,self.p,cost,50)

    def score_budget(self):
        from pysat.card import CardEnc,EncType
        n=self.n;bill=[];D=((0,1),(1,0),(0,-1),(-1,0))
        for i,j in product(range(n),repeat=2):
            s=self.X[i][j];nb=[self.X[i+di][j+dj] for di,dj in D
                              if 0<=i+di<n and 0<=j+dj<n]
            z=self.p.id()
            self.f.append([s,*nb,z])
            for a,b in combinations(nb,2):self.f.append([s,-a,-b,z])
            bill.append(z)
            bill.extend([-s]*(4-len(nb)))
        # One compulsory nonisolated tree; U + join blanks + 4n-D <= 78.
        self.f.extend(CardEnc.atmost(bill,78,vpool=self.p,encoding=EncType.cardnetwrk).clauses)
        from .wired_crop_exchange import ring
        rim=ring(n);gaps=[]
        for (i,j),(u,v) in zip(rim,rim[1:]+rim[:1]):
            gaps.append(self.conj([-self.X[i][j],-self.X[u][v]]))
        self.f.append(gaps)
        self.f.extend(CardEnc.atmost(gaps,7,vpool=self.p,encoding=EncType.cardnetwrk).clauses)
        # Two vertices of an inner 2x2, each touching a marked stub,
        # already belong to the same skeleton tree.
        def anchors(u,v):
            return (self.X[u+(-1 if u%3==1 else 1)][v],
                    self.X[u][v+(-1 if v%3==1 else 1)])
        for i,j in product(range(1,n-1),repeat=2):
            if not(i%3 and j%3):continue
            for a,b in ((i+1,j),(i,j+1)):
                if not(a%3 and b%3):continue
                for s,t in product(anchors(i,j),anchors(a,b)):
                    for z in (self.X[i][j],self.X[a][b]):self.f.append([-s,-t,-z])

    def faces(self):
        """Only extra local masks; the common graph already excludes cyclic ones."""
        from .four_square import masks4
        from .skeleton_wired_faces import face_masks
        good=sorted(face_masks());allgood=(1<<len(good))-1
        sets=[[sum(1<<i for i,m in enumerate(good) if m>>j&1==b)
               for b in (0,1)] for j in range(16)]
        bans=[]
        for m in sorted(set(masks4())-set(good)):
            if any(m&mask==bits for mask,bits in bans):continue
            rem=allgood;mask=0
            while rem:
                j=min(range(16),key=lambda j:(rem&sets[j][m>>j&1]).bit_count())
                mask|=1<<j;rem&=sets[j][m>>j&1]
            bans.append((mask,m&mask))
        assert all(not any(m&mask==bits for mask,bits in bans) for m in good)
        for i,j in product(range(0,self.n-1,3),repeat=2):
            sites=[self.X[i+a][j+b] for a,b in product(range(4),repeat=2)]
            for mask,bits in bans:self.f.append([(-z if bits>>q&1 else z) for q,z in enumerate(sites) if mask>>q&1])

    def segments(self):
        """After transposition every column has a vertical realized edge."""
        from pysat.card import CardEnc,EncType
        n=self.n;cost=[];self.row_used=[]
        for t in (0,1):
            for i in range(0,n,3):
                es=[self.ed[(i,j,0) if t==0 else (j,i,1)] for j in range(0,n-1,3)]
                pre=self.false;prev=self.false
                for e in es:
                    cost.append(self.conj([pre,-prev,e]))
                    pre=self.disj([pre,e]);prev=e
                if t:self.f.append([pre])
                else:cost.append(pre);self.row_used.append(pre)
        # Number of segments is 1+turns: distinct straight segments
        # intersect in the vertices having both axes; there are no four-ways.
        self.f.extend(CardEnc.atmost(cost,38,vpool=self.p,encoding=EncType.cardnetwrk).clauses)
        atleast(self.f,self.p,cost,16)
        return cost

    def sector(self):
        from .diagonal_score import data,cover
        from pysat.pb import PBEnc
        import sys
        assert not any(s.startswith(('--rim-gaps','--three-corners','--four-corners')) for s in sys.argv)
        n=self.n;pos,patch,star,_,budget=data(n,3647)
        cap=16;weights={}
        def charge(tab,sites,guard):
            vals=tuple(cap+1 if z>budget else z*cap//budget for z in tab)
            last=0
            for w in sorted(set(vals)-{0}):
                extra=[]
                if w<=cap:
                    a=self.p.id();weights[a]=w-last;last=w;extra=[a]
                for mask,bits in cover(tuple(v>=w for v in vals)):
                    self.f.append(guard+extra+[(-a if bits>>l&1 else a) for l,a in enumerate(sites) if mask>>l&1])
        D=((0,1),(1,0),(0,-1),(-1,0))
        for i,j in product(range(n),repeat=2):
            if min(i,j,n-1-i,n-1-j)>9:continue
            dirs=self.O[i,j];s=[self.X[i][j],*[self.X[i+D[t][0]][j+D[t][1]] for t in dirs]]
            tab=star(pos(i,j,0),tuple(dirs),len(dirs)==2 and (i or j)!=0)
            for t in [-1,*dirs]:charge(tab[t],s,list(dirs.values()) if t<0 else [-dirs[t]])
            if i<n-2 and j<n-2:charge(patch(pos(i,j,1)),[self.X[i+a][j+b] for a,b in product(range(3),repeat=2)],[])
        self.f.extend(PBEnc.atmost(lits=list(weights),weights=list(weights.values()),bound=cap,
                                   vpool=self.p,encoding=8).clauses)

    def line(self,row):
        f=self.f;zero=self.false;n=self.n
        a=[(row[i-1] if i else zero,row[i],row[i+1] if i+1<n else zero) for i in range(0,n,3)]
        h=[self.disj([l,r]) for l,_,r in a]
        pre=[zero];post=[zero]
        for v in h:pre.append(self.disj([pre[-1],v]))
        for v in h[::-1]:post.append(self.disj([post[-1],v]))
        post.reverse();mixed=pre[-1]
        f.append([mixed,*[-z for _,z,_ in a]])
        for t,(_,z,_) in enumerate(a):
            # A vacant V is either the sole vacancy in a pure row,
            # or hit by at least one of the two next inward stubs.
            left=a[t-1][2] if t else zero;right=a[t+1][0] if t+1<len(a) else zero
            f.append([z,h[t],-mixed,left,right])
            for _,v,_ in a[:t]:f.append([mixed,z,v])
            # Each internal V gap must be a vacant singleton, hit twice.
            for lit in [-z,left,right]:f.append([h[t],-pre[t],-post[t+1],lit])
        for (l,z,r),(L,Z,R) in zip(a,a[1:]):
            # Only one missing predicted slot may be charged per failure,
            # and none on a realized edge.
            f.extend([[-l,r,L,-R],[-l,r,-L,-z],[ -R,L,-r,-Z]])

    def solve(self,tag,seconds,assumptions=()):
        with TemporaryDirectory(prefix='floor-',dir='target') as tmp:
            path=Path(tmp);cnf=path/'in.cnf';proof=path/'proof'
            with cnf.open('w') as out:
                print(f'p cnf {self.f.nv} {len(self.f.clauses)+len(assumptions)}',file=out)
                for c in self.f.clauses:print(*c,0,file=out)
                for x in assumptions:print(x,0,file=out)
            res=subprocess.run(['target/cadical/build/cadical','-t',str(seconds),str(cnf),str(proof)],capture_output=True)
            if res.returncode==20:
                chk=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(proof)],capture_output=True)
                assert chk.returncode==0 and b's VERIFIED' in chk.stdout
                print(tag,'UNSAT, s VERIFIED',flush=True);return 'UNSAT',None
            if res.returncode==10:
                val={int(w) for s in res.stdout.splitlines() if s.startswith(b'v ') for w in s[2:].split()}
                board=[''.join('#' if z in val else '.' for z in row) for row in self.X]
                F,j,A,X=physical(board);assert (j,A,X)==(0,1,0)
                print(tag,'SAT',F,verify(board),flush=True)
                if hasattr(self,'cross'):
                    from .integral_floor_cross import replay_cross
                    replay_cross(self,board,val)
                return 'SAT',board
            assert res.returncode==0,(res.returncode,res.stderr[-1000:])
            print(tag,'UNKNOWN',flush=True);return 'UNKNOWN',None


if __name__=='__main__':
    import sys
    n,F,seconds=map(int,sys.argv[1:4]);m=Floor(n,F)
    if '--faces' in sys.argv:m.faces()
    if '--sector' in sys.argv:m.sector()
    if '--segments' in sys.argv:m.segments()
    cuts=[z for z in sys.argv[4:] if not z.startswith('--')]
    if cuts:
        from .integral_floor_cross import add_cross
        y,x=map(int,cuts);m.cross=(y,x,*add_cross(m,y,x,79 if n==103 else None))
    limit=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--row-limit=')),None)
    if limit is not None:
        from pysat.card import CardEnc
        active=[m.disj([m.ed[i,j,0] for j in range(0,n-1,3)]) for i in range(0,n,3)]
        m.f.extend(CardEnc.atmost(active,limit,vpool=m.p).clauses)
    lower=next((int(z.split('=')[1]) for z in sys.argv if z.startswith('--row-min=')),None)
    if lower is not None:atleast(m.f,m.p,m.row_used,lower)
    print('integral floor',n,'F >=',F,'vars',m.f.nv,'clauses',len(m.f.clauses),flush=True)
    label='unrestricted within floor' if limit is None else f'at most {limit} horizontal edge rows'
    if lower is not None:label+=f' (at least {lower} horizontal edge rows)'
    status,board=m.solve(label,seconds)
    if board and n==103:
        assert verify(board)[-1]==3647
        Path('analysis/research_program/forest_103_floor.txt').write_text('\n'.join(board)+'\n')

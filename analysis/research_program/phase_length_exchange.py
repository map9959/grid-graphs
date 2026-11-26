"""Insert seven rows and columns through a pair of variable phase/bar interfaces."""
from fractions import Fraction as Q
from .full_bar_price import strip
from .detour_separator import horizontal_chunks
from .cheap_cut_mesh import bills
from .comb_cap_transfer import construct
from .extend_forest_28 import verify

def types(rows,i,ev):
    out=[]
    for y,l,r in horizontal_chunks(rows,i,ev):
        word=rows[y][l:r]
        typ='B' if all(v=='#' for v in word) and len(word)>1 else 'P'
        if typ=='P':
            assert any(all((v=='#')==(x%3==p) for x,v in enumerate(word,l)) for p in range(3))
        if out and out[-1][0]==y and typ==out[-1][3]=='B':
            out[-1]=y,out[-1][1],r,typ
        else:out.append((y,l,r,typ))
    return out

def grow(rows,center,chunks):
    """The old horizontal board cut can change level only inside a cleared two-column guard."""
    h=7;H=len(rows);w=len(rows[0]);out=[['.']*w for _ in range(H+h)]
    assert chunks[0][1]==0 and chunks[-1][2]==w
    breaks={l for _,l,_,_ in chunks[1:]}
    guard={x for l in breaks for x in (l-1,l)}
    lost=gain=0
    for y,l,r,typ in chunks:
        assert abs(y-center)<=1
        for x in range(l,r):
            for k in range(H):
                if rows[k][x]=='#':
                    if x in guard and abs(k-center)<=2:lost+=1
                    else:out[k if k<=y else k+h][x]='#'
        lo=l+int(l in breaks);hi=r-int(r in breaks)
        if lo>=hi or typ=='skip':continue
        if typ=='B':
            assert all(rows[y][x]=='#' for x in range(l,r)) and r-l>=2
            word=strip(h,hi-lo)
            for x,b in enumerate(word,lo):
                for j in range(h-1):
                    if b>>j&1:out[y+2+j][x]='#';gain+=1
        else:
            for x in range(lo,hi):
                if rows[y][x]=='#':
                    for j in range(1,h+1):out[y+j][x]='#'
                    gain+=h
    return [''.join(row) for row in out],gain-lost

def two_cuts(rows,i,A,j,B):
    n=len(rows);h=7
    wide,first=grow(rows,i,A)
    # Outside this five-line crossing, the old vertical pieces are
    # translated intact. Through the crossing use a wholly empty insertion.
    lo=max(0,i-2);hi=min(n,i+3)
    def clip(a,b,shift):
        out=[]
        for x,s,t,typ in B:
            l,r=max(s,a),min(t,b)
            if l<r:out.append((x,l+shift,r+shift,typ if r-l>1 or typ!='B' else 'P'))
        return out
    B2=clip(0,lo,0)+[(j,lo,hi+h,'skip')]+clip(hi,n,h)
    out,second=grow(list(zip(*wide)),j,B2)
    return out,first+second

def barlen(c):return sum(r-l for _,l,r,t in c if t=='B')
def price(n,A,B):
    # Per piece: up to 2 unused inserted columns of height density <=7/3,
    # truncating a pitch costs < 7, cutting off the strip motif costs < 3,
    # and up to 10 old marks are deleted per level change.
    F=barlen(A)+barlen(B);K=len(A)+len(B)
    return Q(14*n,3)-Q(4*F,21)-22*(K+2)-12

def holes(rows):
    n=len(rows)
    return [any(r[i][3]=='.' and any(r[i+dy][3+dx]=='#' for dy,dx in
                ((0,-2),(0,-1),(0,1),(0,2),(-1,-1),(-1,1),(1,-1),(1,1)))
                for i in range(9,n-9)) for r in (rows,list(zip(*rows)))]

def check(rows):
    n=len(rows);tr=list(zip(*rows))
    axes=[]
    for rs in (rows,tr):
        cs=[(i,types(rs,i,ev)) for i,ev in bills(rs,None).items()]
        axes.append(min(cs,key=lambda q:Q(4*barlen(q[1]),21)+22*len(q[1])))
    (i,A),(j,B)=axes;out,g=two_cuts(rows,i,A,j,B)
    low=price(n,A,B)
    assert g>=low
    t=verify(out);score=sum(r.count('#') for r in rows)
    assert t[0]==score+g
    m=n+7;k=m//3;U=3*k*k+7*k-(k-5)//7-int(k%14==11)
    assert t[-1]<=U
    print(n,'K',len(A)+len(B),'bar lengths',barlen(A),barlen(B),'gain',g,
          'tree',t,'returned upper',U-g,'input',score,'guard failures',holes(rows))

def puncture(rows,y,x):
    pts=[list(r) for r in rows]
    for a in range(-2,3):
        for b in range(-2+abs(a),3-abs(a)):pts[y+a][x+b]='.'
    pts[y][x]='#'
    return [''.join(r) for r in pts]

def witnesses(n):
    rows=construct(n,4);near=puncture(rows,n//2,2)
    assert sum(r.count('#') for r in near)==sum(r.count('#') for r in rows)-3
    assert all(holes(near));print('avoider tree',verify(near));check(near)
    # Vertical pitch in a central band, horizontal bars elsewhere.
    # Two empty rows disconnect consecutive regions.
    a,b=n//3,2*(n//3)
    mixed=['.'*n if a-2<=i<a or b<=i<b+2 else rows[3] if a<=i<b else
           ('#' if i%3==0 else '.')*n for i in range(n)]
    mixed=puncture(mixed,2,n//2)
    assert all(holes(mixed));print('mixed tree',verify(mixed));check(mixed)

if __name__=='__main__':
    # Worst prefix discrepancy of the actual full-bar motif, then one
    # whole period repeats with exactly the required increment.
    from .full_bar_price import MOTIF
    prefix,cycle=MOTIF[7]
    err=max(Q(15*l,7)-sum(b.bit_count() for b in strip(7,l)) for l in range(len(prefix)+len(cycle)+1))
    assert err<=3
    print('one-period worst bar truncation debit',err)
    for n in (103,193):witnesses(n)

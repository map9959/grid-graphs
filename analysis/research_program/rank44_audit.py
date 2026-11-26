"""Independent small-board check of the line-exception debit and face labelling."""
from itertools import product
from collections import Counter
from .rank44_faces import table,labels
from .four_square import masks4
from .patch_square import trans
from .pitch_skeleton_ledger import ledger
from .skeleton_floor_words import next_state,finish


def missed(row):
    st={('pre',None,0),('p0',None,0)}
    for j in range(0,len(row),3):
        a=tuple(int(0<=h<len(row) and row[h]=='#') for h in (j-1,j,j+1))
        st={u for s in st if (u:=next_state(s,a)) is not None}
    return not any(map(finish,st))


def check(rows):
    n=len(rows);pitch='#..'*(n//3)+'#'
    tx=[''.join(c) for c in zip(*rows)]
    if pitch in rows or pitch in tx:return
    for words in (rows,tx):
        M,F,_,_,C,_=ledger(words,empty='V')
        X=n*(n//3+1)+F-C-M
        assert sum(missed(w) for w in words[::3])<=X
    return True


def audit():
    lib=masks4();samples=0;orbits=0
    for m in lib:
        rows=[''.join('#' if m>>(4*y+x)&1 else '.' for x in range(4)) for y in range(4)]
        samples+=bool(check(rows))
    for C,j in ((1,0),(2,0),(2,1)):
        T=table(C,j)
        for (m,q),v in T.items():
            for g,im in enumerate(lib[m][1]):
                part=sum((q>>a&1)<<(2*r+c) for a in range(4)
                         for r,c in [trans(a//2,a%2,2,g)])
                assert T[im,part^(15 if part&1 else 0)]==v
                orbits+=1
    # Embed pairs of independent admissible tiles with a blank rail
    # between them: includes internal line gaps absent on side four.
    import random
    rng=random.Random(44);ms=list(lib)
    for _ in range(10000):
        n=10;rows=[['.']*n for _ in range(n)]
        for y,x in product((0,6),repeat=2):
            m=rng.choice(ms)
            for a,b in product(range(4),repeat=2):
                if m>>(4*a+b)&1:rows[y+a][x+b]='#'
        samples+=bool(check([''.join(r) for r in rows]))
    print('no-pitch line-debit controls',samples,'rank-preserving face transforms',orbits)
    # Independent full-size histogram: orbit-normalize physical face
    # counts, then expand by distinct images as the LP does. Compare
    # to ordered transitions on all eight transformed whole boards.
    from fractions import Fraction
    mark=[[rng.randrange(2) for _ in range(103)] for _ in range(103)]
    color=[[rng.randrange(2) for _ in range(35)] for _ in range(35)]
    ff=Counter();ll=Counter();cache={}
    for i,j in product(range(0,102,3),repeat=2):
        cells=[(i+a,j+b) for a,b in product(range(4),repeat=2)]
        imgs=set()
        for g in range(8):
            a,b=trans(i,j,100,g);tag=labels(a,b,100,2)
            bits=[0]*16;c=0
            for n,(y,x) in enumerate(cells):
                r,s=trans(n//4,n%4,4,g)
                bits[4*r+s]=mark[y][x]
                if r%3==s%3==0:c|=color[y//3][x//3]<<(2*(r//3)+s//3)
            imgs.add((tag,tuple(bits),c^15 if c&1 else c))
        k=min(imgs);cache[k]=imgs;ff[k]+=1
    for g in range(8):
        for i,j in product(range(0,103,3),range(0,102,3)):
            word=tuple(mark[u][v] for z in range(j,j+4) for u,v in [trans(i,z,103,g)])
            for a in (0,3):
                if 0<=i-a<100:ll[labels(i-a,j,100,2),a,word]+=1
    for k,v in ff.items():
        imgs=cache[k]
        for tag,bits,_ in imgs:
            for a in (0,3):ll[tag,a,bits[4*a:4*a+4]]-=Fraction(8*v,len(imgs))
    assert not any(ll.values())
    print('full-size word transport: all',1156*2*8,'rotated face-side readings agree')


if __name__=='__main__':audit()

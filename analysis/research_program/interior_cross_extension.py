"""One-column and one-row subdivision anywhere in a physical square."""
from .dense_joint_collar import upper,comb,marks
from .extend_forest_28 import verify

def tp(rows):return [''.join(col) for col in zip(*rows)]

def centers(a,b):
    w=[x=='#' or y=='#' for x,y in zip(a,b)]
    return [i for i,t in enumerate(w) if t and not(i and w[i-1]) and not(i+1<len(w) and w[i+1])]

def pack(s,ban=()):
    p=[]
    for j in s:
        if j not in ban and (not p or j-p[-1]>=3):p.append(j)
    return p

def put(rows,j,p):
    s=['.']*len(rows[0])
    for k in p:s[k]='#'
    return rows[:j+1]+[''.join(s)]+rows[j+1:]

def best(rows):
    cols=tp(rows)
    horiz=[centers(a,b) for a,b in zip(rows,rows[1:])]
    vert=[centers(a,b) for a,b in zip(cols,cols[1:])]
    h=[pack(s) for s in horiz];v=[pack(s) for s in vert];bestpair=(-1,None)
    for y,hs in enumerate(h):
        for x,vs in enumerate(v):
            if len(hs)+len(vs)<=bestpair[0]:continue
            if (x in hs or x+1 in hs) and (y in vs or y+1 in vs):
                h2=pack(horiz[y],(x,x+1));v2=pack(vert[x],(y,y+1))
                hp,vp=(h2,vs) if len(h2)+len(vs)>=len(hs)+len(v2) else (hs,v2)
            else:hp,vp=hs,vs
            z=len(hp)+len(vp)
            if z>bestpair[0]:bestpair=z,(x,y,hp,vp)
    gain,(x,y,hp,vp)=bestpair
    ext=tp(put(tp(put(rows,y,hp)),x,[j+(j>y) for j in vp]))
    assert marks(ext)==marks(rows)+gain
    tree=verify(ext);assert tree[-1]>=marks(ext)
    n=len(rows)
    return gain,upper(n+1)-gain,(len(hp),len(vp)),tree

if __name__=='__main__':
    from .dense_joint_collar import punctures
    from .comb_cap_transfer import construct
    from .arbitrary_collar_transfer import obstruction_board
    for label,r in [('comb',construct(103,4)),('mixed',obstruction_board(103,True)[1]),('double',punctures(103,True))]:
        print(label,best(verify(r,True)))

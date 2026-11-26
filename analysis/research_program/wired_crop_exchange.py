"""Extract a four-side wired crop and replay the reverse frame construction."""
from .extend_forest_28 import verify

def ring(s):
    return ([(0,x) for x in range(s)]+[(y,s-1) for y in range(1,s)]+
            [(s-1,x) for x in reversed(range(s-1))]+[(y,0) for y in reversed(range(1,s-1))])

def parts(m,marks):
    p=list(range(m*m))
    def rt(i):
        while p[i]!=i:p[i]=p[p[i]];i=p[i]
        return i
    for y in range(m):
        for x in range(m):
            for u,v in ((y+1,x),(y,x+1)):
                if max(u,v)>=m or ((y,x) not in marks and (u,v) not in marks):continue
                a,b=rt(y*m+x),rt(u*m+v);assert a!=b;p[a]=b
    return {z:rt(z[0]*m+z[1]) for z in ring(m)}

def extract(rows):
    n=len(rows);m=n-4;marks={(y,x) for y,r in enumerate(rows) for x,c in enumerate(r) if c=='#'}
    R=ring(n);g=sum(R[j] not in marks and R[j-1] not in marks for j in range(len(R)))
    holes=sum(p not in marks for p in R);corners=sum((y,x) not in marks for y in (0,n-1) for x in (0,n-1))
    D1={(y,x) for y,x in marks if min(y,x,n-1-y,n-1-x)==1}
    crop={(y-2,x-2) for y,x in marks if min(y,x,n-1-y,n-1-x)>=2}
    comp=parts(m,crop);teeth=set(comp)&crop;back=[];unback=[]
    for y,x in sorted(teeth):
        feet=[]
        if not y:feet.append((0,x+2))
        if y==m-1:feet.append((n-1,x+2))
        if not x:feet.append((y+2,0))
        if x==m-1:feet.append((y+2,n-1))
        (back if any(f in marks for f in feet) else unback).append((y,x))
    assert len(D1)+len(unback)<=holes+corners
    distinct={comp[t] for t in back};assert len(back)-len(distinct)<=g-1
    keep={comp[t]:t for t in sorted(teeth)}
    crop-=teeth-set(keep.values());C=parts(m,crop)
    assert len({C[t] for t in crop if t in C})==len(crop&set(C))
    assert len(marks)<=len(crop)+4*n-5+corners+g
    return crop,g,len(marks)-len(crop)

def reframe(m,crop):
    n=m+4;R=set(ring(n))-{(0,1),(0,2),(1,n-1),(n-1,n-2),(n-2,0)}
    pts=R|{(y+2,x+2) for y,x in crop if not (y in (0,m-1) and x in (0,m-1))}
    rows=[''.join('#' if (y,x) in pts else '.' for x in range(n)) for y in range(n)]
    return verify(rows)

def near_sides(m,crop):
    """Put the crop one site from north/west, two from south/east."""
    n=m+3
    d=sum(bool({(0,j),(1,j)}&crop)+bool({(j,0),(j,1)}&crop) for j in range(m))
    kept={(i,j) for i,j in crop if min(i,j)>=1 and
          (i!=1 or (0,j) in crop) and (j!=1 or (i,0) in crop) and
          not(i in (1,m-1) and j in (1,m-1))}
    assert len(crop)-len(kept)<=d+4
    R=set(ring(n))-{(0,1),(0,2),(1,n-1),(n-1,n-2),(n-2,0)}
    pts=R|{(i+1,j+1) for i,j in kept}
    v=verify([''.join('#' if (i,j) in pts else '.' for j in range(n)) for i in range(n)])
    if m%3==0:assert len(crop)<=m*m//3-m+5+d
    return d,v

def far_sides(m,crop):
    """Duplicate north and west tooth words; each new line subdivides a root spoke."""
    T=sum(((0,j) in crop)+((j,0) in crop) for j in range(m))
    inner={(i,j) for i,j in crop if not(i in (0,m-1) and j in (0,m-1))}
    grown={(i+1,j+1) for i,j in inner}|{(0,j+1) for i,j in inner if i==0}|{(i+1,0) for i,j in inner if j==0}
    assert len(grown)>=len(crop)+T-8
    parts0=parts(m+1,grown);teeth=set(parts0)&grown
    assert len({parts0[v] for v in teeth})==len(teeth)
    tree=reframe(m+1,grown);assert tree[0]==len(grown)+4*(m+5)-9
    return T,tree

def audit():
    from .comb_cap_transfer import construct
    from .zipper_rails import build
    for rows in (construct(103,4),construct(112,4),build(119)):
        crop,g,lost=extract(rows);n=len(rows)
        print(n,'rim gaps',g,'wired crop',len(crop),'loss',lost,'frame replay',reframe(n-4,crop))
        if n%3==1:
            print('adjacent-side exchange',near_sides(n-4,crop))
            print('residue-two exchange',far_sides(n-4,crop))
if __name__=='__main__':audit()

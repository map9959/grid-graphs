"""Lift a billed row to a simple cut with only full and pitch pieces."""
from .cheap_cut_mesh import bills,bit
from .comb_cap_transfer import construct

def horizontal_chunks(rows,i,events):
    n=len(rows);mark=lambda y,x:rows[y][x]=='#'
    pieces=[];a=0;live=set(range(5))
    for x in range(n):
        opts={j for j in range(5) if bit(j,x)==mark(i,x)}
        if not live&opts:pieces.append((a,x,min(live)));a=x;live=opts
        else:live&=opts
    pieces.append((a,n,min(live)))
    e=len(events);assert len(pieces)<=1+2*e
    chunks=[]
    for a,b,q in pieces:
        if q<4:chunks.append((i,a,b));continue
        cuts={a,b}
        for x in events:
            if a<=x<b:cuts.update((x,x+1))
        cuts=sorted(cuts)
        for l,r in zip(cuts,cuts[1:]):
            if r-l<=2:
                for x in range(l,r):chunks.append((i,x,x+1))
                continue
            chunks.append((i,l,l+1))
            x=l+1
            while x<r-1 and mark(i+1,x):x+=1
            if x>l+1:chunks.append((i+1,l+1,x))
            if x<r-1:
                assert all(mark(i-1,j) for j in range(x,r-1))
                chunks.append((i-1,x,r-1))
            chunks.append((i,r-1,r))
    K=len(chunks);assert K<=4+13*e
    return chunks

def detour(rows,i,events):
    chunks=horizontal_chunks(rows,i,events);K=len(chunks);n=len(rows)
    mark=lambda y,x:rows[y][x]=='#'
    path=[]
    for y,l,r in chunks:
        if path:
            old=path[-1][0]
            step=1 if y>old else -1
            path.extend((z,l) for z in range(old,y,step))
        path.extend((y,x) for x in range(l,r))
    P=set(path);assert len(P)==len(path)<=n+2*(K-1)
    marks=sum(mark(*v) for v in P)
    edges=sum(mark(y,x) or mark(u,v) for y,x in P for u,v in ((y+1,x),(y,x+1)) if (u,v) in P)
    C=len(P)-edges
    assert abs(len(P)-marks-2*C)<=10*K
    return K,len(P)-n,len(P)-marks-2*C

if __name__=='__main__':
    for n in (103,193,403):
        board=construct(n,4);res=[detour(rows,i,events) for rows in (board,list(zip(*board)))
                                  for i,events in bills(rows).items()]
        print(n,len(res),'cuts; max chunks, extra sites, absolute terminal discrepancy:',
              *(max(abs(z[j]) for z in res) for j in range(3)))

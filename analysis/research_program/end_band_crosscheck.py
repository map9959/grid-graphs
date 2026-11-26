"""Direct small-grid enumeration with two bands competing for the same exterior components."""
from itertools import product
from .end_band_rank import refill,verify
from .sparse_component_exchange import Forest

def check():
    n=16;l,r=2,7;ys=(3,11);centers=(3,6)
    seen=0
    for outer in ((),(1,),(5,9),(1,5,9,13)):
        rows=['#'*n if i in outer else '.'*n for i in range(n)]
        # The word at an exterior backing line can be full, empty, or
        # attached to other backing lines in the same component.
        for connected in (False,True):
            board=[('#'+row[1:]) if connected and i==7 else row for i,row in enumerate(rows)]
            touches=[(y+s,x) for y in ys for x in centers for s in (-1,1)]
            best=-1
            for mask in range(256):
                marks={(i,j) for i,row in enumerate(board) for j,v in enumerate(row) if v=='#'}
                marks.update(product(ys,centers));marks.update(v for s,v in enumerate(touches) if mask>>s&1)
                G=Forest(n)
                if all(G.join((i,j),(u,v)) for i in range(n) for j in range(n)
                       for u,v in ((i+1,j),(i,j+1)) if u<n and v<n and ((i,j) in marks or (u,v) in marks)):
                    best=max(best,len(marks))
            ans=refill(board,ys,l,r,centers,False)
            assert (ans is None)==(best<0)
            if ans:assert sum(row.count('#') for row in ans[0])==best
            seen+=256
    print(seen,'physical normal-row masks: exact maxima and infeasible cases matched')
    # Only change marks outside the two tiles and their backing triples.
    # The remote connection turns the second independent join of the
    # first tooth into a cycle; both teeth compete for the same pair.
    prices=[]
    for bridge in (False,True):
        board=['#'*n if i in (1,7) else
               '#'+'.'*(n-1) if bridge and i in (3,5) else '.'*n
               for i in range(n)]
        verify(board)
        out,price=refill(board,[4],l,r,centers,False)
        verify(out);prices.append(price[3])
    assert prices==[3,2]
    print('identical bands and backing triples, optional ranks:',*prices)
if __name__=='__main__':check()

"""Partition-free run-plus-component charge for teeth on all four sides."""
from itertools import product
from .arbitrary_collar_transfer import marks

def debit(rows):
    n=len(rows);words=[]
    for _ in range(4):
        words.append(rows[0]);rows=list(map(''.join,zip(*rows[::-1])))
    def price(w,left,right):
        d=[0]
        for j,x in enumerate(w):
            tooth=x=='#' and (w[j-1]=='.' if j else left) and (w[j+1]=='.' if j+1<n else right)
            d.append(max(d[-1],int(tooth)+d[max(j-2,0)]))
        return d[-1]
    # The top row after clockwise rotation is the previous left column
    # read backwards: its right endpoint is the previous left endpoint.
    t=max(sum(price(w,choice[i],not choice[i-1]) for i,w in enumerate(words))
          for choice in product((True,False),repeat=4))
    # Start/finish corner indexing: right of i = left of i-1.
    def bars(w):
        return sum(len(z)>=2 for z in w.strip('#').split('.') if z)
    extra=min(bars(words[0])+bars(words[2]),bars(words[1])+bars(words[3]))
    D=sum(w.count('#') for w in words)
    return t+extra,D

def upper(rows):
    t,D=debit(rows)
    return (len(rows)**2+D-t)//3

def exhaustive(n=4):
    from .extend_forest_28 import verify
    count=0
    for bits in range(1<<(n*n)):
        r=[''.join('#' if bits>>(n*y+x)&1 else '.' for x in range(n)) for y in range(n)]
        try:verify(r)
        except AssertionError:continue
        assert bits.bit_count()<=upper(r),(r,debit(r));count+=1
    print(count,'feasible small-square markings satisfy the four-side debit')

def check():
    from .comb_cap_transfer import construct
    from .dense_joint_collar import punctures,verify
    from .crop_end_coupling import locked_fringe
    for n in (103,133):
        for name,r in [('comb',construct(n,4)),('locked',locked_fringe(n)),('double',punctures(n,True))]:
            r=verify(r,True);c=[s[9:-9] for s in r[9:-9]]
            u=upper(c);assert u>=marks(c)
            t=marks(r)-marks(c)
            print(n,name,'outer nine',t,'core ledger terms',debit(c),'core upper',u,'sum',u+t)
            if name=='comb':assert u==marks(c)
if __name__=='__main__':exhaustive();check()

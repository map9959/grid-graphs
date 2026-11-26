"""The joint cap price allows each cut window to choose its own row."""
from .comb_cap_transfer import construct

def bound(rows):
    n=len(rows);assert n%3==1
    r=(n+2)//3;w=3*r;tr=[]
    for a in (rows,[''.join(t) for t in zip(*rows)]):
        # Padding two blank columns costs no marks and separates copies.
        a=[row+'..' for row in a]
        for phase in range(3):
            words=[sum((row[(3*i+phase)%w]=='#' and row[(3*i+phase-1)%w]==row[(3*i+phase+1)%w]=='.')<<i
                       for i in range(r)) for row in a]
            z=0
            for q in words:z|=q
            good=0
            for i in range(r):
                req=sum(1<<((i+j)%r) for j in range(11)) if r>=11 else (1<<r)-1
                # The two extreme halo cells need to be blank on the
                # marker row as well.
                good+=any(q&req==req and row[(3*i+phase-2)%w]==row[(3*(i+10)+phase+2)%w]=='.'
                          for row,q in zip(a,words))
            price=n*r+(88*r-22*z.bit_count()-8*good)//44
            tr.append((price,z.bit_count(),good))
    assert min(tr)[0]>=sum(row.count('#') for row in rows)
    return min(tr)

if __name__=='__main__':
    for n in (103,133,193):print(n,bound(construct(n,4)))

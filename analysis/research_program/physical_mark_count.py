"""A carry-save binary mark counter; exclude each prefix less than target."""
from itertools import product
from collections import deque

def add(f,pool,sites,target):
    assert 0<target<=len(sites)
    col=deque(sites);digits=[]
    while col:
        carry=deque()
        while len(col)>1:
            v=[col.popleft() for _ in range(min(3,len(col)))]
            s=pool.id();c=pool.id()
            for bits in product(range(2),repeat=len(v)):
                f.append([x*(-1 if b else 1) for x,b in zip(v,bits)]+[s*(1 if sum(bits)%2 else -1)])
            if len(v)==2:
                a,b=v;f.extend([[-a,-b,c],[a,-c],[b,-c]])
            else:
                a,b,d=v
                for x,y in ((a,b),(b,d),(d,a)):f.extend([[-x,-y,c],[x,y,-c]])
            carry.append(c);col.append(s)
        digits.append(col[0]);col=carry
    for i,x in enumerate(digits):
        if target>>i&1:f.append([x,*[digits[j]*(-1 if target>>j&1 else 1) for j in range(i+1,len(digits))]])

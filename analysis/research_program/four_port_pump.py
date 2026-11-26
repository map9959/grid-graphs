"""Check two bulk insertions at (possibly different) cuts of an accepting walk."""
from collections import defaultdict
from itertools import combinations_with_replacement

def certificate(graph,west,suffix,axis):
    # For each small exact closed-walk type record every possible anchor.
    loops=defaultdict(set)
    for p in graph:
        st={p:1}
        for n in range(1,7):
            nxt={}
            for v,b in st.items():
                for w,c in graph[v]:nxt[w]=nxt.get(w,0)|(b<<c)
            st=nxt;b=st.get(p,0)
            while b:
                one=b&-b;loops[n,one.bit_length()-1].add(p);b-=one
    def verify(A,B,h):
        def flags(p):return int(p in loops[A])+2*int(p in loops[B])
        st={(p,flags(p)):b for p,b in west.items() if p in graph}
        for j in range(25+14*(h-1)):
            nxt={}
            for (p,f),b in st.items():
                for q,c in graph[p]:
                    key=q,f|flags(q)
                    nxt[key]=nxt.get(key,0)|(b<<c)
            st=nxt
            if j>=24 and (j-24)%14==0:
                D=198+72*((j-24)//14)
                if not any(f==3 and any((v>>c)&1 and (b>>(D-c))&1 for c in range(min(v.bit_length(),D+1)))
                           for (p,f),b in st.items() if (v:=suffix.get(p,0))):
                    return False
        return True
    # Each base residue needs an accepted walk which visits both types.
    # Adding copies at those two vertices preserves ALL ordered interfaces.
    for h in (1,2,3,6):
        attempts=[]
        for A,B in combinations_with_replacement(loops,2):
            for x in range(1,(14*h)//A[0]+1):
                rem=14*h-A[0]*x;y,r=divmod(rem,B[0])
                if not r and y>0 and A[1]*x+B[1]*y==72*h:
                    attempts.append((-(len(loops[A])*len(loops[B])),A,B,x,y))
        for _,A,B,x,y in sorted(attempts):
            if verify(A,B,h):
                print('axis',axis,'all-t certificate: t step',h,'insert',x,'x',A,'and',y,'x',B,
                      '(columns,deficit); all',h,'base budgets reached with both anchors',flush=True)
                return True
    return False

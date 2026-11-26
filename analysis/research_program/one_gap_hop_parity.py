"""Does the unaveraged GF(2) count obstruction improve after eliminating forbidden hops?"""
from collections import defaultdict
from itertools import product
from .odd_frames import prep,evaluate,frame
from .defect_window import table,DIR

def run():
    n=203;T,_,S=table(n);data=prep();cols,q,lab,rd,mass,bits,rhs=data
    dep=lambda i,j:min(i,j,n-1-i,n-1-j)
    def bucket(t,x):
        h=6-t;s=n-2*t
        return x if x<h else 2*h+6+x-s if x>=s-h else h+(x-h)%6
    def key(t,i,j):return (t,bucket(t,i),bucket(t,j))
    def eligible(i,j):return min(i,j)==2 and 5<=max(i,j)<=n-6 and max(i,j)%6==5
    patches=defaultdict(set)
    for i,j in product(range(n-2),repeat=2):
        pairs=[]
        for s,t in product(range(3),repeat=2):
            x,y=i+s,j+t
            for d,(a,b) in enumerate(DIR[:2]):
                if max(s+2*a,t+2*b)>2:continue
                z,w=x+2*a,y+2*b
                if min(dep(x,y),dep(z,w))<2:continue
                pref=lambda x,y,e:dep(x,y)>=3 and not S(T(0,x,y),(0,1,2,3),e,False,False)[1]
                if not(pref(x,y,d) or pref(z,w,d+2)):
                    e=(1<<(3*s+t))|(1<<(3*(s+2*a)+t+2*b));m=1<<(3*(s+a)+t+b)
                    pairs.append((e,m))
        patches[key(1,i,j)].add((tuple(pairs),eligible(i+1,j+1)))
    clean={k:{m for m in range(512) if any((iso or m&186) and
                         all(m&e!=e or m&mid for e,mid in pairs) for pairs,iso in st)} for k,st in patches.items()}
    for w in product((1,3),repeat=3):
        word=(0,*w);fr=frame(n,word);stars=defaultdict(set)
        for i,j in product(range(n),repeat=2):
            feet=tuple(d for d,(a,b) in enumerate(DIR) if dep(i,j)==2 and dep(i+2*a,j+2*b)==0 and fr[i+2*a,j+2*b])
            stars[key(0,i,j)].add((dep(i,j)==2,feet,eligible(i,j)))
        qq=q.copy()
        for h,(k,e) in enumerate(lab):
            if qq[h]>72:continue
            if k[0]:ok=not q[h] and e in clean[k]
            else:
                v,nb,out=e;degree=nb.count(1)
                ok=any(((v or degree) and not q[h] and
                        (not shell or (feet==(out,) if v else degree==1))) or
                       (iso and not v and degree==0 and out==-1 and q[h]==72)
                       for shell,feet,iso in stars[k])
            if not ok:qq[h]=73
        result=evaluate((cols,qq,lab,rd,mass,bits,rhs),word)[0] # 203=35+4*42
        print(''.join(map(str,word)),'phase-five surviving site buckets',sorted({k[1:] for k,e in result}),flush=True)
if __name__=='__main__':run()

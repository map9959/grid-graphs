"""Two rail spans separated by a freely optimized rewiring seam."""
from itertools import product
import subprocess,sys

def run(n,h,m,k,bars,check=()):
    assert n%3==1 and m and n>=h+m+k+2*bars.bit_count()+2
    seq=[];edges=[];fixed=[];ix={};cp=[]
    def vertex(key,fix=-1):
        assert key not in ix;ix[key]=len(seq);seq.append(key);edges.append([]);fixed.append(fix)
    def edge(u,v,always=False):
        i,j=sorted((ix[u],ix[v]));edges[j].append((i,always))
    for s in (0,1):
        if bars>>s&1:vertex(('bar',s),0)
    for j in range(n):
        rail=(j+1)//3
        if j==0 or j%3==2:
            for s in (0,1):vertex(('rail',rail,s),0)
        for t,H in enumerate((h,m,k)):
            for z in range(H):
                p=(t,z,j);vertex(p)
                if j:edge(p,(t,z,j-1))
                if z:edge(p,(t,z-1,j))
            if t==1:
                edge((t,0,j),('rail',rail,0),j%3==0)
                edge((t,H-1,j),('rail',rail,1),j%3==0)
            else:
                s=t//2
                if H:
                    edge((t,0,j),('rail',rail,s),j%3==0)
                    if bars>>s&1:edge((t,H-1,j),('bar',s))
                elif bars>>s&1 and j%3==0:edge(('rail',rail,s),('bar',s),True)
        if j in check:cp.append(len(seq)-1)
    N=len(seq)
    txt=' '.join(map(str,[N,*[a for es in edges for a in (len(es),*(i+1+N*int(f) for i,f in es))],*fixed,*cp]))
    p=subprocess.run(['target/annular_frontier'],input=txt,text=True,capture_output=True,check=True)
    cap,W,peak=map(int,p.stdout.split());q=n//3
    total=(n-2*bars.bit_count()-h-m-k)*(q+1)+bars.bit_count()*n+cap
    comb=3*q*q+5*q+(3*q-13)//10
    print('n',n,'bands',h,m,k,'bars',bars,'width',W,'states',peak,'score',total,'gain',total-comb,p.stderr.strip(),flush=True)
    return total
if __name__=='__main__':run(*map(int,sys.argv[1:6]),check=list(map(int,sys.argv[6:])))

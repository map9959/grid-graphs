"""Two wholly free caps tied by the actual common rail terminals."""
import subprocess,sys

def run(n,h,k,check=()):
    ix={};adj=[];fixed=[];cp=[]
    def add(key,f):
        ix[key]=len(adj);adj.append([]);fixed.append(f)
    def edge(u,v,always=False):
        a,b=sorted((ix[u],ix[v]));adj[b].append((a,always))
    for j in range(n):
        r=('rail',(j+1)//3)
        if r not in ix:add(r,0)
        for s,d in enumerate((h,k)):
            for i in range(d):
                p=s,i,j;add(p,-1)
                if j:edge(p,(s,i,j-1))
                if i:edge(p,(s,i-1,j))
                else:edge(p,r,j%3==0)
        if j in check:cp.append(len(adj)-1)
    N=len(adj);inp=[N,*[a for ls in adj for a in (len(ls),*(i+1+N*u for i,u in ls))],*fixed,*cp]
    pr=subprocess.run(['target/annular_frontier'],input=' '.join(map(str,inp)),text=True,capture_output=True,check=True)
    val,w,peak=map(int,pr.stdout.split());r=n//3
    score=val+(n-h-k)*(r+1);comb=3*r*r+5*r+(3*r-13)//10
    print(n,'free caps',h,k,'states',peak,'score',score,'gain',score-comb,pr.stderr.strip(),flush=True)
    return score
if __name__=='__main__':run(*map(int,sys.argv[1:4]),check=list(map(int,sys.argv[4:])))

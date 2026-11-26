"""Propose labels for the existing three finite duals; Lean rechecks all coefficients."""
from collections import defaultdict
from pathlib import Path
from .patch_square import relaxation, trans
from .rank44_faces import table

DEST = Path(__file__).resolve().parents[2]/'lean/GridGraphs/NoPitch/FiniteRows'


def scan(n):
    data = iter((DEST.parent/'Data'/f'chart{n}.v32').read_bytes())
    def u():
        t = next(data)-48
        return t if t<32 else t-32+32*u()
    def z():
        a=u(); return -(a//2)-1 if a%2 else a//2
    _,nr,nc = u(),u(),u()
    rows = [(u(),u(),z(),z(),z(),z()) for _ in range(nr)]
    cols=[]; masks=[0]*nr
    for _ in range(nc):
        key,units,fix,obj,c=u(),u(),u(),z(),u(); i=0; ts={}
        for _ in range(c):
            i+=u(); ts[i]=z(); masks[i]|=[1,1,4,8,2,16][key%8]
        cols.append((key,units,ts))
    return rows,cols,masks


def export(n):
    rows,cols,masks=scan(n)
    tags=[]; relaxation(n,8,pooled=4,period=3,diagonal=4,tags=tags)
    lines=['import GridGraphs.NoPitch.TailRows.IncidenceChecks','import GridGraphs.NoPitch.TailRows.FaceLineChecks',
           'namespace GridGraphs.NoPitch.FiniteRows','open TailRows LocalBoard19']
    parts=[]
    for kind in ['s','sp','pp']:
        tokens=[]; ids=[]
        for i,(src,*_) in enumerate(rows):
            if src>=len(tags):continue
            sign,tag=tags[src];
            if tag[0]!=kind:continue
            _,a,b,d,*etc=tag;w=etc[-1];v=3*(2*w[0]+w[1])+w[2]+1 if kind=='s' else sum(x<<j for j,x in enumerate(w)); t=0
            for x in [*a[:2],4+a[2],4+a[3],*b[:2],4+b[2],4+b[3],d]:t=t*32+x
            ids.append(i);tokens.append(2*(64*t+v)+(sign<0))
        assert ids==list(range(ids[0],ids[-1]+1));parts.append((ids[0],ids[-1]+1))
        lines += [f'private def {kind}{n} : Array Nat := #[',',\n'.join(','.join(map(str,tokens[i:i+8])) for i in range(0,len(tokens),8))+']']
    a,b,c=(p[0] for p in parts); end=parts[-1][1]
    lines += [f'def inc{n} : Incidence.Book := ⟨{a},{b},{c},{end},tagMap s{n} {a},tagMap sp{n} {b},tagMap pp{n} {c}⟩']
    # Recover each face-line label from its coefficient vector on decoded faces.
    cand=defaultdict(dict); obs=defaultdict(dict)
    for key,units,terms in cols:
        if key%8!=2:continue
        a=key//8; p,m=a>>24,(a>>8)%65536
        r,c=p//32//3,p%32//3
        for g in range(8):
            x,y=trans(r,c,3,g); inv=g if g>=4 else -g%4
            for d in [0,1]:
                word=0
                for j in range(4):
                    h,l=trans(3*d,j,4,inv);word|=(m>>(4*h+l)&1)<<j
                token=(((3*x*7+3*y)*2+d)*16+word);cand[token][key]=1+cand[token].get(key,0)
        for i,v in terms.items():
            if masks[i]==12:obs[i][key]=units*v
    # D4-equivalent horizontal labels can have identical face coefficients
    # but different line coefficients. Recover the common original row offset.
    order = list(dict.fromkeys((d,sum((m>>(12*d+j)&1)<<j for j in range(4)))
                               for m,_ in table(4,3) for d in (0,1)))
    keys = [(((x*7+y)*2+d)*16+word) for x in (0,3,6) for y in (0,3,6) for d,word in order]
    ids=sorted(obs); assert ids==list(range(ids[0],ids[-1]+1))
    offsets=[rows[ids[0]][0]-j for j,t in enumerate(keys) if cand[t]==obs[ids[0]]]
    offsets=[s for s in offsets if all(0<=rows[i][0]-s<len(keys) and cand[keys[rows[i][0]-s]]==obs[i] for i in ids)]
    start,=offsets; tokens=[keys[rows[i][0]-start] for i in ids]
    lines += [f'def fl{n} : FaceLine.Book := ⟨{ids[0]},#['+','.join(map(str,tokens))+']⟩', 'end GridGraphs.NoPitch.FiniteRows\n']
    (DEST/f'Book{n}.lean').write_text('\n'.join(lines))

if __name__=='__main__':
    for n in (22,25,52): export(n)

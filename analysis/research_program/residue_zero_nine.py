"""Side-nine cycle cuts and sequential-cardinality LRAT proof."""
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

def clauses():
    def cnt(i,j):
        return 6643+i*36+j
    for i in range(81):
        for j in range(35):
            yield [-cnt(i+1,j+1),cnt(i,j+1),i+1]
            yield [-cnt(i+1,j+1),cnt(i,j)]
    for j in range(35):
        yield [-cnt(0,j+1)]
    yield [cnt(81,35)]
    for p in range(81):
        for q in [p+1,p+9]:
            if q<81 and (p%9<8 or q!=p+1):
                g = 82+81*p+q
                yield [-g,-1-p]
                yield [-g,-1-q]


def rectangles():
    for a in range(9):
        for b in range(9):
            for u in range(a+1,9):
                for v in range(b+1,9):
                    yield ([9*a+j for j in range(b,v)] + [9*i+v for i in range(a,u)]
                           + [9*u+j for j in range(v,b,-1)] + [9*i+b for i in range(u,a,-1)])


def main():
    root = Path(__file__).resolve().parents[2]
    lean = root/'lean'
    dest = lean/'GridGraphs/ResidueZero'
    solver = Path(subprocess.check_output(['lean','--print-prefix'],cwd=lean,text=True).strip())/'bin/cadical'
    rows = list(clauses())
    def cut(vs):
        return [82+81*min(p,q)+max(p,q) for p,q in zip(vs,vs[1:]+vs[:1])]
    for vs in rectangles():
        rows.append(cut(vs))
    extra = []
    with TemporaryDirectory(dir=dest) as tmp:
        src,proof = (Path(tmp)/s for s in ['nine.cnf','nine.lrat'])
        while True:
            src.write_text(f'p cnf {max(abs(v) for c in rows for v in c)} {len(rows)}\n'
                           + ''.join(' '.join(map(str,c))+' 0\n' for c in rows))
            r = subprocess.run([solver,'--lrat','--no-binary',src,proof],capture_output=True)
            if r.returncode==20:
                break
            assert r.returncode==10
            true = {int(v)-1 for line in r.stdout.decode().splitlines() if line.startswith('v ')
                    for v in line.split()[1:] if 1<=int(v)<=81}
            seen=set()
            def dfs(v,stack):
                seen.add(v)
                for w in [v-9,v-1,v+1,v+9]:
                    if (not 0<=w<81 or abs(w//9-v//9)+abs(w%9-v%9)!=1 or
                        (v not in true and w not in true)):continue
                    if w not in seen:
                        dfs(w,stack+[v])
                    elif w in stack[:-1]:
                        yield_cycle(stack[stack.index(w):]+[v])
            def yield_cycle(vs):
                for g in range(8):
                    ds=[]
                    for v in vs:
                        i,j=divmod(v,9)
                        if g&4:j=8-j
                        for _ in range(g%4):i,j=j,8-i
                        ds.append(9*i+j)
                    extra.append(ds);rows.append(cut(ds))
            old=len(extra)
            for v in range(81):
                if v not in seen:dfs(v,[])
            assert len(extra)>old
        (dest/'nine.lrat').write_bytes(proof.read_bytes())
        with (dest/'NineCycles.lean').open('w') as out:
            print('namespace GridGraphs.ResidueZero.Nine\n\ndef extraCycles : List (List Nat) := [',file=out)
            print(',\n'.join(map(str,extra))+']\n\nend GridGraphs.ResidueZero.Nine',file=out)
        print('extra cycles:',len(extra),'LRAT proof bytes:',proof.stat().st_size)


if __name__=='__main__':
    main()

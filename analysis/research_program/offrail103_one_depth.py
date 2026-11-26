"""First empty depth on the normalized unique empty side of a 3647 board."""
import hashlib,json,shutil,subprocess,sys
from itertools import combinations
from pathlib import Path
from .offrail103_depth_split import band,verify,N

BASE=Path('target/offrail103_survivors/one.cnf')
HASH='ae60c4fafd6f1354ecca7b2e5d140bed96767fa67a1777bcbb9dda3608407ef4'
def suffix(d,top):
    assert 2<=d<=10
    rows=[band(0,i) for i in range(2,d)]+[[-x] for x in band(0,d)]
    def two(vs):
        nonlocal top
        # A true flag certifies a mark with an earlier distinct mark.
        pairs=[];prefix=vs[0]
        for x in vs[1:]:
            z,p=top+1,top+2;top+=2
            rows.extend([[-z,x],[-z,prefix],[-p,prefix,x]])
            pairs.append(z);prefix=p
        return pairs
    if d<=4:
        for g in (1,3):
            for j in (2,3,4):rows.append(two(band(g,j)))
    # On each adjacent pair, one side has two or more depth-seven marks.
    flags=[two(band(g,7)) for g in range(4)]
    for g in range(4):rows.append(flags[g]+flags[(g+1)%4])
    # In the unique-empty-north case the two certified projections
    # require this threshold on *both* west and east individually.
    for g in (1,3):rows.append(flags[g])
    for g in (1,3):
        by_row={}
        for x in band(g,7):by_row.setdefault((x-1)//N,[]).append(x)
        occupied=[]
        for vs in by_row.values():
            top+=1;occupied.append(top)
            rows.append([-top,*vs])
        rows.append(two(occupied))
        rows.extend(separation_clauses(g))
        rows.extend(separation_clauses(g,last=16))
    return top,rows

def separation_clauses(side,last=N-1):
    # Eligible row indices are 1,2,4,5,...,100,101. To get a
    # separated pair, marks cannot all belong to any one row doublet.
    xs=[x for x in band(side,7) if (x-1)//N<=last]
    groups=sorted({(x-1)//N//3 for x in xs})
    return [[x for x in xs if (x-1)//N//3!=t] for t in groups]

def group_cut(top,part):
    assert part in ('west','east')
    groups=[];rows=[]
    for side in (1,3):
        xs=band(side,7)
        for t in range(6):
            marks=[x for x in xs if (x-1)//N<=16 and (x-1)//N//3==t]
            top+=1;groups.append(top)
            rows.append([-top,*marks]);rows.extend([[-x,top] for x in marks])
    w,e=groups[:6],groups[6:]
    rows.extend(map(list,combinations(groups,8)))  # at least five of twelve
    rows.extend(map(list,combinations(w if part=='west' else e,4)))
    if part=='east':rows.extend([-a,-b,-c] for a,b,c in combinations(w,3))
    return top,rows

def run(sec,depths,part=None):
    with BASE.open('rb') as src:assert hashlib.file_digest(src,'sha256').hexdigest()==HASH
    dest=Path('target/offrail103_one_depth_adj7_corner16'+('_groups5_'+part if part else ''));dest.mkdir(exist_ok=True)
    for d in depths:
        stem=dest/f'd{d}';cnf=stem.with_suffix('.cnf');pr=stem.with_suffix('.drat')
        with BASE.open('rb') as src,cnf.open('wb') as out:
            _,_,v,c=src.readline().split();top,extra=suffix(d,int(v))
            if part:
                top,more=group_cut(top,part);extra.extend(more)
            out.write(f'p cnf {top} {int(c)+len(extra)}\n'.encode());shutil.copyfileobj(src,out)
            for ls in extra:out.write((' '.join(map(str,ls))+' 0\n').encode())
        with cnf.open('rb') as fd:sha=hashlib.file_digest(fd,'sha256').hexdigest()
        with stem.with_suffix('.log').open('wb') as fd:
            rc=subprocess.run(['target/cadical/build/cadical','-t',str(sec),str(cnf),str(pr)],stdout=fd).returncode
        if rc==20:
            out=subprocess.run(['target/drat-trim/drat-trim',str(cnf),str(pr)],check=True,capture_output=True).stdout
            assert b's VERIFIED' in out;stem.with_suffix('.check').write_bytes(out);result='VERIFIED UNSAT'
        elif rc==10:
            model={int(x) for line in stem.with_suffix('.log').read_text().splitlines() if line.startswith('v ') for x in line[2:].split()}
            board=[''.join('#' if i*N+j+1 in model else '.' for j in range(N)) for i in range(N)]
            replay=verify(board);assert replay[-1]>=3647
            stem.with_suffix('.txt').write_text('\n'.join(board)+'\n');result=str(replay)
        else:
            assert rc==0 and 'UNKNOWN' in stem.with_suffix('.log').read_text()
            pr.unlink(missing_ok=True);result='UNKNOWN'
        cnf.unlink();stem.with_suffix('.json').write_text(json.dumps(dict(depth=d,seconds=sec,sha256=sha,result=result))+'\n')
        print('first empty',d,result,flush=True)
if __name__=='__main__':run(int(sys.argv[1]),[int(s) for s in sys.argv[2:] if not s.startswith('--')],next((s[7:] for s in sys.argv if s.startswith('--part=')),None))

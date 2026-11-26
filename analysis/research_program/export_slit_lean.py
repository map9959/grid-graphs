"""Export finite automata, not inclusion verdicts, for the Lean replay."""
from pathlib import Path
from .slit_width_induction import attempt
from .ranked_slit_prices import ALL, ZERO, EMPTY
from .cap_site_arrows import build,extend_sites

DEST = Path(__file__).resolve().parents[2] / 'lean/GridGraphs/Geometry/SlitData'


def series(nums, chunk=12):
    vals=list(map(str,nums))
    return ',\n'.join(','.join(vals[i:i+chunk]) for i in range(0,len(vals),chunk))


def export():
    DEST.mkdir(exist_ok=True)
    prefix='import GridGraphs.Geometry.SlitProduct\n\nnamespace GridGraphs.Slit.Data\n'
    suffix='\nend GridGraphs.Slit.Data\n'
    layers,get,_=attempt(28,2,5,1500,False,None,False,extend_sites)
    ids={};defs=[]

    def tag(d):
        rows,final=d
        assert len(rows)<511 and all(0<=c<8 for row in rows for c in row)
        codes=[0]+[sum((v+1) << (9*c) for c,v in r.items()) for r in rows]
        mask=sum(1<<(s+1) for s in final)
        key=tuple(codes),mask
        if key not in ids:
            i=ids[key]=len(ids)
            defs.append(f'def d{i} : DFA := ⟨#[{series(codes)}],'
                        f' (Array.range {len(codes)}).map (Nat.testBit {mask})⟩\n')
        return ids[key]

    assert [tag(d) for d in (EMPTY,ALL,ZERO)]==[0,1,2]
    table=[]
    for n in range(26):
        tabs=[]
        for s in range(12):
            if s not in layers[n]:tabs.append('none');continue
            low,_=layers[n][s]
            tabs.append(f'some ({low},#[{series(tag(get(n,s,z)) for z in range(low,5))}])')
        table.append('#['+series(tabs,4)+']')
    packs=[]
    for start in range(0,len(defs),15):
        name=f'DFA{start//15}';packs.append(name)
        (DEST/f'{name}.lean').write_text(prefix+'\n'.join(defs[start:start+15])+suffix)
    locals=[]
    for edge,drop in [('L',0),('L',1),('',0),('',1)]:
        name=f'Local{len(locals)}';states,arcs,ends=build(edge,drop)
        assert len(arcs)<512
        rows=['['+series(x+8*y+64*v+32768*z for x,y,v,z in r)+']' for r in arcs]
        loc=f'def t{len(locals)} : Local := ⟨#[{series(rows,1)}],#[{series(ends.get(i,-1)+1 for i in range(len(arcs)))}]⟩'
        loc+=f'\ndef states{len(locals)} : Array Nat := #[{series(m+32*a+1024*u+8192*f for m,a,u,f in states)}]\n'
        locals.append(name)
        (DEST/f'{name}.lean').write_text(prefix+loc+suffix)
    rev=lambda c: 2*(c%2)+(c//2)%2+4*int(bool(c%4) and c<4)
    # Stepping on letter 4 is immaterial: it is not a physical slit letter.
    t4=f'def reflect : Local := ⟨#[[{series(x+8*rev(x) for x in range(8))}]],#[1]⟩'
    main='\n'.join('import GridGraphs.Geometry.SlitData.'+name for name in packs+locals)
    main+='\n\nnamespace GridGraphs.Slit.Data\n'+t4+'\n'
    main+=f'def langs : Array DFA := #[{series(f"d{i}" for i in range(len(defs)))}]\n'
    main+='def localTables : Array Local := #[t0,t1,t2,t3,reflect]\n'
    main+='def siteStates : Array (Array Nat) := #[states0,states1,states2,states3]\n'
    main+='def layers : Array (Array (Option (Int × Array Nat))) := #[\n'+series(table,1)+']\n'
    (DEST/'Tables.lean').write_text(main+suffix)
    print('exported',len(defs),'DFAs, 4 weighted transducers, reflection and 26 layers')


if __name__=='__main__':export()

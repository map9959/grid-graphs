"""Check the exact chart data committed for Lean, not producer internals.

All sets are unbounded integer lattice regions. The checks below are the
physical coverage and local turn-closure implications of LowerTurnTable.
"""
from pathlib import Path
from .residue_two_lower_turns import BASES, DIRS, mask, poly, shift


def region(line):
    s=[]
    for op in line.split():
        if op in ('t','i','j') or op.lstrip('-').isdigit():s.append(op)
        elif op=='T':s.append('(1=1)')
        elif op=='F':s.append('(1=0)')
        elif op=='~':s.append(f'(-{s.pop()})')
        else:
            b,a=s.pop(),s.pop()
            if op=='/':z=f'floor(({a})/{b})'
            elif op=='%':z=f'(({a}) mod {b})'
            else:
                token={'&':'and','|':'or','G':'>=','L':'<=','g':'>','l':'<',
                       '=':'=','+':'+','-':'-','*':'*'}[op]
                z=f'({a} {token} {b})'
            s.append(z)
    assert len(s)==1
    return poly('[t]->{[i,j] : '+s[0]+'}').clean()


def audit(base):
    root=Path(__file__).resolve().parents[2]/"lean/GridGraphs/Constructions/ResidueTwo/LowerTurnData"
    lines=(root/f'base{base}.turns').read_text().splitlines()
    assert len(lines)%4==0
    area=poly(f'[t]->{{[i,j]: t>=0 and 0<=i<{base}+42t and 0<=j<{base}+42t}}')
    m=area.op('intersect',poly('[t]->{[i,j]:'+mask(base)+'}')).clean()
    edges=[region(l) for l in lines[:4]]
    for d in range(4):
        sh=shift(d).op('reverse')
        forced=m.op('union',m.op('apply',sh)).op('intersect',area).op('intersect',area.op('apply',sh))
        assert forced.op('subtract',edges[d]).empty(),(base,'coverage',d)
    old=edges
    for s in range(1,len(lines)//4+1):
        new=[region(l).op('intersect',e).clean() for l,e in zip(
            lines[4*s:4*s+4] or ['F']*4,edges)]
        for d in range(4):
            for e in (d,(d+1)%4,(d+3)%4):
                nexts=new if d==e else old
                required=nexts[e].op('apply',shift(d).op('reverse')).op('intersect',edges[d])
                assert required.op('subtract',new[d]).empty(),(base,s,d,e)
        old=new
    print(f'{base}: physical coverage and {len(lines)//4} turn layers verified',flush=True)


if __name__=='__main__':
    import sys
    for base in list(map(int,sys.argv[1:])) or BASES:audit(base)

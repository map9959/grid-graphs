"""Export proposed incidence tags at the two parity bases only."""
import json
from pathlib import Path
from .patch_square import relaxation


def export(n, source):
    here = Path(__file__).resolve().parent
    dest = here.parents[1] / 'lean/GridGraphs/NoPitch/TailRows'
    tags = []
    relaxation(n, 8, pooled=4, period=3, diagonal=4, tags=tags)
    rows = json.loads((here/f'free_width_{source}.json').read_text())
    lines = ['namespace GridGraphs.NoPitch.TailRows']
    for kind,name in [('s','edge'),('sp','cell'),('pp','pair')]:
        tokens = []
        indices = []
        for i,(r,_) in enumerate(rows):
            if r >= len(tags):
                continue
            sign,tag = tags[r]
            if tag[0] != kind:
                continue
            _,p,q,d,*rest = tag
            w = rest[-1]
            v = 3*(2*w[0]+w[1])+w[2]+1 if kind=='s' else sum(b<<j for j,b in enumerate(w))
            key = 0
            for a in [*p[:2],p[2]+4,p[3]+4,*q[:2],q[2]+4,q[3]+4,d]:
                key = key*32+a
            tokens.append(str(2*(key*64+v)+(sign<0)))
            indices.append(i)
        assert indices == list(range(indices[0],indices[-1]+1))
        lines += [f'def {name}Start{n} := {indices[0]}', f'def {name}Tags{n} : Array Nat := #[']
        lines.append(',\n'.join(','.join(tokens[j:j+8]) for j in range(0,len(tokens),8))+']')
    lines.append('end GridGraphs.NoPitch.TailRows\n')
    (dest/f'IncidenceTags{n}.lean').write_text('\n'.join(lines))


if __name__=='__main__':
    export(58,106)
    export(61,103)

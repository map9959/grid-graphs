"""Compact semantic row tags for Lean's side-19 physical overlap checks."""
from pathlib import Path
import json
from .patch_square import relaxation


def export():
    tags = []
    relaxation(19, 8, pooled=4, period=3, diagonal=4, tags=tags)
    rows = json.loads(Path(__file__).with_name('free_width_19.json').read_text())
    out = Path(__file__).resolve().parents[2] / 'lean/GridGraphs/NoPitch/Budget'

    def pack(xs):
        n = 0
        for d in xs:
            n = 32*n+d
        return n

    def spatial(p):
        a,b,c,d = p
        return [a,b,4+c,4+d]

    for family,first,last in [('s',13,343),('sp',344,1163),('pp',1164,1927)]:
        tokens = []
        for i in range(first,last+1):
            sign,(kind,p,q,*rest) = tags[rows[i][0]]
            assert kind == family
            word = rest.pop()
            if kind == 's':
                a,b,s = word
                v = 3*(2*a+b)+s+1
            else:
                v = sum(a<<j for j,a in enumerate(word))
                if kind == 'pp':
                    rest = [rest[0]]
            tokens.append(str(2*(pack(spatial(p)+spatial(q)+rest)*64+v)+(sign<0)))
        lines = [','.join(tokens[j:j+8]) for j in range(0,len(tokens),8)]
        name = {'s':'edgeTokens','sp':'starPatchTokens','pp':'pairTokens'}[family]
        (out/(name+'.lean')).write_text(
            'namespace GridGraphs.NoPitch.LocalBoard19\n'
            '/-- Candidate overlap tags, verified against the decoded matrix. -/\n'
            f'def {name} : Array Nat := #[\n'+',\n'.join(lines)+']\n'
            'end GridGraphs.NoPitch.LocalBoard19\n')


if __name__ == '__main__':
    export()

"""Encode the published residue-zero prices as integral Lean lookup tables."""
import json
from fractions import Fraction
from pathlib import Path


def pos(p):
    return p[0] * 16 + p[1]


def bits(xs):
    return sum(x << i for i, x in enumerate(xs))


def encode(k):
    kind, p, *args = k
    if not args:
        return pos(p)
    t, *mid, event = args
    if kind == 's':
        f, nb, arrow = event
        idx, val = mid[0], 3*(2*f+nb)+arrow+1
    else:
        idx = mid[0]  # sp: patch offset; pp: first displacement (0=east, 1=south)
        val = bits(event)
    return ((pos(p)*256+pos(t))*9+idx)*64+val


def main():
    here = Path(__file__).resolve().parent
    entries = json.loads((here/'square_dual_stencil_r0.json').read_text())
    dest = here.parents[1]/'lean/GridGraphs/ResidueZero/Prices.lean'
    with dest.open('w') as out:
        print('import Std\n\n/-! Integral prices from `square_dual_stencil_r0.json`.\n'
              'Regenerate with `python3 -m analysis.research_program.residue_zero_lean_stencil`. -/\n'
              'namespace GridGraphs.ResidueZero\n\ndef scale : Int := 4373984', file=out)
        for tag, name in [('corner', 'corner'), ('star norm', 'starNorm'),
                          ('patch norm', 'patchNorm'), ('s', 'edge'),
                          ('sp', 'incidence'), ('pp', 'overlap')]:
            table = {}
            for k, q in entries:
                if k[0] == tag:
                    v = Fraction(q)*4373984
                    assert v.denominator == 1 and encode(k) not in table
                    table[encode(k)] = int(v)
            pairs = ',\n  '.join(f'({k}, {v})' for k, v in table.items())
            print(f'\ndef {name}Prices : Std.HashMap Nat Int := .ofList [\n  {pairs}]', file=out)
        print('\nend GridGraphs.ResidueZero', file=out)


if __name__ == '__main__':
    main()

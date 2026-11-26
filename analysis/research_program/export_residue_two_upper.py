"""Reproduce the residue-two period-three sparse dual from its saved multipliers.

Run as `python3 -B -m analysis.research_program.export_residue_two_upper`.
No solver or floating-point arithmetic. The row polynomials come from the
symbolic axis multiplicities checked in repeating_patch_dual.polynomial.
"""
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

from .patch_square import SYM, trans
from .repeating_patch_dual import filename, polynomial


def column_key(atom):
    kind, ((r, c), *rest) = atom
    if kind == 'p':
        mask, = rest
        return 2 * ((r * 16 + c) * 512 + mask) + 1
    mark, neighbours, arrow = rest
    code = (r * 16 + c) * 2 + mark
    for value in neighbours:
        code = 10 * code + value  # missing = 9
    return 2 * (5 * code + arrow + 1)


def stabilizer(atom):
    kind, (fine, *rest) = atom
    n, d = (18, 5) if kind == 'p' else (20, 6)
    i, j = (v if v < d+3 else v+5 for v in fine)

    def axis(v):
        return v if v < d else v-5 if v >= n-d else d+(v-d)%3
    images = []
    for g in range(8):
        p = tuple(axis(v) for v in trans(i, j, n, g))
        if kind == 'p':
            images.append((p, SYM[rest[0]][g]))
        else:
            mark, nb, arrow = rest
            def turn(s):
                return ((2-s if g & 4 else s)+(g & 3)) % 4
            rotated = [9]*4
            for s, value in enumerate(nb):
                rotated[turn(s)] = value
            images.append((p, mark, tuple(rotated), turn(arrow) if arrow >= 0 else -1))
    assert min(images) == atom[1]
    return images.count(atom[1])


def export():
    base, names, matrix, rhs, obj = polynomial(2, 3)
    digest, pairs = json.loads(filename(2, 3, 2).read_text())
    assert base == 20
    assert digest == hashlib.sha256(repr((matrix, rhs, sorted(obj.items()))).encode()).hexdigest()
    data = bytearray()

    def unsigned(x):
        assert x >= 0
        while x >= 32:
            data.append(80 + x % 32)
            x //= 32
        data.append(48 + x)

    def signed(x):
        unsigned(2*x if x >= 0 else -2*x-1)

    scale = math.lcm(*(Fraction(v).denominator for _, v in pairs))
    unsigned(scale)
    unsigned(len(pairs))
    unsigned(len(names))
    cols = {x: [] for x in names.values()}
    for j, (i, v) in enumerate(pairs):
        row, op = matrix[i]
        unsigned(i)
        unsigned({'=': 0, '<=': 1, '>=': 2}[op])
        signed(int(Fraction(v)*scale))
        a, b, c = rhs[i]
        for w in (2*a, 2*b-c, c):
            signed(w)
        for x, w in row:
            cols[x].append((j, w))
    assert len({column_key(atom) for atom in names}) == len(names)
    for atom, x in names.items():
        unsigned(column_key(atom))
        units = stabilizer(atom)
        marked = atom[0] == 's' and atom[1][1]
        assert obj.get(x, 0) * units == (8 if marked else 0)
        unsigned(units)
        unsigned(0)  # unrestricted: no fixed columns
        signed(obj.get(x, 0))
        unsigned(len(cols[x]))
        prev = 0
        for j, w in cols[x]:
            unsigned(j-prev)
            signed(w)
            prev = j
    dest = Path(__file__).resolve().parents[2] / 'lean/GridGraphs/ResidueTwoUpper/Data'
    dest.mkdir(exist_ok=True, parents=True)
    (dest / 'periodThree.v32').write_bytes(data + b'\n')


if __name__ == '__main__':
    export()

"""Audit the ordinary SE bank and the eleven-word closed-corner extension.

Run from workspace root with PYTHONPATH=target/pb-python. No data or
proof logs are produced. SAT is only used as an external diagnostic,
not as a Lean proof of physical admission.
"""
from itertools import product
from pathlib import Path
import gzip
import json

from pysat.solvers import Solver
from analysis.research_program.arm_budget_bands import transpose
from analysis.research_program.defect_window import table, window
from analysis.research_program.fan_speed_cover import Pool
from analysis.research_program.fan_speed_replay import native
from analysis.research_program.odd_frames import frame

EXTRA = {
    (10, 11): {(6,48,6,33), (6,48,7,33), (7,48,7,33), (16,48,7,33),
               (288,128,292,32), (292,128,292,32), (384,192,288,32), (448,192,288,32)},
    (10, 12): {(48,24,33,24), (128,24,32,24), (192,24,32,24)},
}


def end_tag(extent, i):
    return 6 if i + 8 <= extent else 14 + i - extent


def ordinary():
    raw = Path("target/tile_family_3_5_h6.json.gz").read_bytes()
    return {(a,b): set(map(tuple, ws)) for a,b,ws in json.loads(gzip.decompress(raw))
            if a >= 6 and b >= 6}


def export_bank():
    def encode(word):
        key = sum(m << (9*i) for i,m in enumerate(word))
        return "".join(chr(48 + ((key >> (6*i)) & 63)) for i in range(6))
    bank = ordinary()
    rows = ("".join(encode(w) for w in sorted(bank[tag])) for tag in sorted(bank))
    Path(__file__).with_name("SouthCapBank.txt").write_text("\n".join(rows)+"\n")


def audit():
    original = ordinary()
    widened = {tag: ws | EXTRA.get(tag, set()) for tag,ws in original.items()}
    n = 119
    prices = table(n)
    for se in (1, 3):
        marks = frame(n, (1, 1, se, 1))
        for tag, ws in widened.items():
            x,y = (1 + 3*(31 if t == 6 else t+25) for t in tag)
            dom = set(product(range(x-6, min(n,x+12)), range(y-6, min(n,y+12))))

            def emit(f, bit, _flags):
                for p in sorted(dom & marks.keys()):
                    f.append([bit(*p)*(1 if marks[p] else -1)])
                cells = [[bit(x+3*a+i,y+3*b+j) for i,j in product(range(3), repeat=2)]
                         for a,b in product(range(2), repeat=2)]

                def forbid(word):
                    return [-v if m>>i&1 else v for m,vs in zip(word,cells) for i,v in enumerate(vs)]

                with Solver(name="cadical195", bootstrap_with=f.clauses) as sol:
                    for word in sorted(original[tag]):
                        sol.add_clause(forbid(word))
                    outside = set()
                    while sol.solve():
                        model = set(sol.get_model())
                        word = tuple(sum((v in model)<<i for i,v in enumerate(vs)) for vs in cells)
                        outside.add(word)
                        assert word in ws, (se, tag, word)
                        sol.add_clause(forbid(word))
                    if outside:
                        print("closed corner", se, "tag", tag, "additional words", sorted(outside))
            window(n, "rim", 1, prices, want=False, root_site=(n-1,n-1),
                   domain=dom, emit=emit)
    # The strip engine expects transposed masks, with horizontal tag first.
    bank = {(b,a): frozenset(tuple(transpose(z[i]) for i in (0,2,1,3)) for z in ws)
            for (a,b),ws in widened.items()}
    for h in range(14,44):
        w = 3*h//4 + 3
        p = Pool()
        g = []
        for y,x in product(range(h-1), range(w-1)):
            ws = bank[end_tag(w,x),end_tag(h,y)]
            g.append(p.intern(ws if y else frozenset(z for z in ws if z[0]==z[2]==7)))
        assert not native(g,p,w,h,(),w-1,True,sides=2), h
    print("ordinary and widened words:", sum(map(len,original.values())), sum(map(len,widened.values())))
    print("all 30 rooted cap rectangles rejected, no axis filters")


if __name__ == "__main__":
    import sys
    if sys.argv[1:] == ["--export-bank"]:
        export_bank()
    else:
        audit()

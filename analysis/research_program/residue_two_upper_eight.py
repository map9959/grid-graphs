"""Generate the side-eight rectangle-only LRAT certificate (single CaDiCaL).

The Lean theorem reconstructs every clause and checks the proof. Temporary
DIMACS and solver output stay in the passed workspace directory.
"""
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory


def clauses():
    def count(i, j):
        return 4096 + 64 + i*29 + j
    def gap(p, q):
        p, q = sorted((p, q))
        return 64 + p*64 + q
    def rect(a, b, u, v):
        return ([8*a+j for j in range(b, v)] + [8*i+v for i in range(a, u)]
                + [8*u+j for j in range(v, b, -1)] + [8*i+b for i in range(u, a, -1)])
    # Literals below use signed DIMACS numbering (internal id + 1).
    for i in range(64):
        for j in range(28):
            y = -1-count(i+1, j+1)
            yield [y, 1+count(i, j+1), 1+i]
            yield [y, 1+count(i, j)]
    for j in range(28):
        yield [-1-count(0, j+1)]
    yield [1+count(64, 28)]
    for p in range(64):
        for q in (p+1, p+8):
            if q >= 64 or (q == p+1 and p%8 == 7):
                continue
            yield [-1-gap(p, q), -1-p]
            yield [-1-gap(p, q), -1-q]
    for a in range(8):
        for b in range(8):
            for u in range(a+1, 8):
                for v in range(b+1, 8):
                    vs = rect(a, b, u, v)
                    yield [1+gap(p, vs[(i+1)%len(vs)]) for i, p in enumerate(vs)]


def main():
    root = Path(__file__).resolve().parents[2]
    lean = root / 'lean'
    cadical = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=lean,
                                            text=True).strip()) / 'bin/cadical'
    cs = list(clauses())
    with TemporaryDirectory(dir=root/'target') as td:
        input_file = Path(td)/'eight.cnf'
        lrat = Path(td)/'eight.lrat'
        input_file.write_text(f'p cnf {max(abs(v) for c in cs for v in c)} {len(cs)}\n'
                              + ''.join(' '.join(map(str, c))+' 0\n' for c in cs))
        result = subprocess.run([cadical, '--lrat', '--no-binary', input_file, lrat],
                                stdout=subprocess.DEVNULL)
        assert result.returncode == 20
        print('LRAT bytes:', lrat.stat().st_size)
        dest = lean/'GridGraphs/ResidueTwoUpper/Data/eight.lrat'
        dest.write_bytes(lrat.read_bytes())


if __name__ == '__main__':
    main()

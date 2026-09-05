#!/usr/bin/env python3
"""Emit exact SMT-LIB for the uniform coupled-interval affine formula."""

from pathlib import Path

import argparse

from coupled_interval_formula import constraints


def term(row: tuple[int, ...]) -> str:
    summands = []
    for index, coefficient in enumerate(row):
        if coefficient:
            summands.append(f"(* {coefficient} x{index})")
    if not summands:
        return "0"
    if len(summands) == 1:
        return summands[0]
    return f"(+ {' '.join(summands)})"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--widths", type=int, nargs="+", default=list(range(3, 7)))
    parser.add_argument("--output", type=Path,
                        default=Path("/tmp/opencode/coupled-interval-formula.smt2"))
    args = parser.parse_args()
    names, inequalities = constraints(sorted(set(args.widths)))
    lines = ["(set-option :produce-models true)", "(set-logic QF_LRA)"]
    lines.extend(f"(declare-const x{index} Real) ; {name}" for index, name in enumerate(names))
    lines.extend(f"(assert (<= {term(row)} {rhs}))" for row, rhs in inequalities)
    lines.extend(["(check-sat)", "(get-value (" + " ".join(f"x{i}" for i in range(len(names))) + "))"])
    args.output.write_text("\n".join(lines) + "\n")
    print(len(names), len(inequalities))


if __name__ == "__main__":
    main()

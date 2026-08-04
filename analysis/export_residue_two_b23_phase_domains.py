#!/usr/bin/env python3
"""Export exact B23 row-mask domains for the compiled frontier search."""

from __future__ import annotations

import argparse
from pathlib import Path

from search_residue_two_b_state_phase_pump import row_domains


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--mode", choices=("basic", "targeted", "phase"), default="phase")
    parser.add_argument("--radius", type=int, default=3)
    args = parser.parse_args()
    _, _, _, domains = row_domains(args.radius, args.mode)
    args.output.write_text("".join(",".join(map(str, domain)) + "\n" for domain in domains))
    print(f"wrote {args.output}: {[len(domain) for domain in domains]}")


if __name__ == "__main__":
    main()

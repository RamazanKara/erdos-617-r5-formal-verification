#!/usr/bin/env python3
"""Check and decode a complete exact-K26 DIMACS model to coloring format."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.check_dimacs_model import check_model, read_cnf, read_model  # noqa: E402
from src.generate_full_k26_cnf import COLORS, ORDER, variable  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("cnf", type=Path)
    parser.add_argument("model", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    variables, clauses = read_cnf(args.cnf)
    assignment = read_model(args.model, variables)
    check_model(clauses, assignment)

    lines = [f"ERDOS617-COLORING-V1 {ORDER} {COLORS} 6"]
    color_counts = [0] * COLORS
    for left, right in itertools.combinations(range(ORDER), 2):
        present = [
            color
            for color in range(COLORS)
            if assignment[variable(left, right, color) - 1]
        ]
        if len(present) != 1:
            raise ValueError(f"edge {left} {right} has {len(present)} colors")
        color = present[0]
        color_counts[color] += 1
        lines.append(f"{left} {right} {color}")

    raw = ("\n".join(lines) + "\n").encode("ascii")
    args.output.write_bytes(raw)
    print(
        "FULL-K26-MODEL-DECODE-PASS "
        f"variables={variables} clauses={len(clauses)} "
        f"color_counts={','.join(map(str, color_counts))} "
        f"sha256={hashlib.sha256(raw).hexdigest()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

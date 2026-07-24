#!/usr/bin/env python3
"""Generate depth-three cubes for the hard E014 u4455_a1 branch."""

from __future__ import annotations

import argparse
from pathlib import Path

from src.generate_local_209_double_classified_u50_full_canonical_cnf import (
    build_instance,
)
from src.generate_local_209_u50_a1_depth2_cnf import render as render_parent

THIRD_VARIABLE = 499
THIRD_NAME = ("exceptional-edge", 0, 15, 19)


def render(
    first_positive: bool,
    second_positive: bool,
    third_positive: bool,
) -> str:
    cnf, _ = build_instance("u4455_a1")
    if cnf.names.get(THIRD_NAME) != THIRD_VARIABLE:
        raise AssertionError("E014 depth-three variable/name mapping changed")
    lines = render_parent(first_positive, second_positive).splitlines()
    for index, line in enumerate(lines):
        if line.startswith("p cnf "):
            fields = line.split()
            lines[index] = f"p cnf {fields[2]} {int(fields[3]) + 1}"
            break
    else:
        raise AssertionError("E014 depth-two parent omitted its DIMACS header")
    lines.append(f"{THIRD_VARIABLE if third_positive else -THIRD_VARIABLE} 0")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--first", choices=("positive", "negative"), required=True)
    parser.add_argument("--second", choices=("positive", "negative"), required=True)
    parser.add_argument("--third", choices=("positive", "negative"), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(
        render(
            args.first == "positive",
            args.second == "positive",
            args.third == "positive",
        ),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

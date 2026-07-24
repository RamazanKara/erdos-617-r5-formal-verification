#!/usr/bin/env python3
"""Generate the four exhaustive depth-two cubes for hard E014 u4455_a1."""

from __future__ import annotations

import argparse
from pathlib import Path

from src.generate_local_209_double_classified_u50_full_canonical_cnf import (
    build_instance,
)
from src.generate_local_209_u50_a1_split_cnf import render as render_parent

SECOND_VARIABLE = 498
SECOND_NAME = ("exceptional-edge", 0, 15, 18)


def render(first_positive: bool, second_positive: bool) -> str:
    cnf, _ = build_instance("u4455_a1")
    if cnf.names.get(SECOND_NAME) != SECOND_VARIABLE:
        raise AssertionError("E014 depth-two variable/name mapping changed")
    lines = render_parent(first_positive).splitlines()
    for index, line in enumerate(lines):
        if line.startswith("p cnf "):
            fields = line.split()
            lines[index] = f"p cnf {fields[2]} {int(fields[3]) + 1}"
            break
    else:
        raise AssertionError("E014 split parent omitted its DIMACS header")
    lines.append(f"{SECOND_VARIABLE if second_positive else -SECOND_VARIABLE} 0")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--first", choices=("positive", "negative"), required=True)
    parser.add_argument("--second", choices=("positive", "negative"), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(
        render(args.first == "positive", args.second == "positive"),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

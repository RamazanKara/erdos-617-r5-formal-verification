#!/usr/bin/env python3
"""Split the hard E014 (+,-) leaf on a balanced edge-count counter."""

from __future__ import annotations

import argparse
from pathlib import Path

from src.generate_local_209_double_classified_u50_full_canonical_cnf import (
    build_instance,
)
from src.generate_local_209_u50_a1_depth2_cnf import render as render_parent

SPLIT_VARIABLE = 6829
SPLIT_NAME = ("counter", "exceptional-edge-count", 0, 105, 25)


def render(positive: bool) -> str:
    cnf, _ = build_instance("u4455_a1")
    if cnf.names.get(SPLIT_NAME) != SPLIT_VARIABLE:
        raise AssertionError("E014 balanced-counter variable/name mapping changed")
    lines = render_parent(True, False).splitlines()
    for index, line in enumerate(lines):
        if line.startswith("p cnf "):
            fields = line.split()
            lines[index] = f"p cnf {fields[2]} {int(fields[3]) + 1}"
            break
    else:
        raise AssertionError("E014 (+,-) parent omitted its DIMACS header")
    lines.append(f"{SPLIT_VARIABLE if positive else -SPLIT_VARIABLE} 0")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--polarity", choices=("positive", "negative"), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(
        render(args.polarity == "positive"),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

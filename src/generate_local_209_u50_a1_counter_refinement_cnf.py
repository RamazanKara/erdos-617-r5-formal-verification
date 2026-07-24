#!/usr/bin/env python3
"""Refine the positive direct u50_a1 counter branch at the next threshold."""

from __future__ import annotations

import argparse
from pathlib import Path

from src.generate_local_209_balanced_counter_split_cnf import render as render_parent
from src.generate_local_209_double_classified_u50_full_canonical_cnf import (
    build_instance,
)

SPLIT_VARIABLE = 6830
SPLIT_NAME = ("counter", "exceptional-edge-count", 0, 105, 26)


def render(positive: bool) -> str:
    cnf, _ = build_instance("u4455_a1")
    if cnf.names.get(SPLIT_NAME) != SPLIT_VARIABLE:
        raise AssertionError("E014 next counter-threshold mapping changed")
    lines = render_parent("u50_a1", True).splitlines()
    for index, line in enumerate(lines):
        if line.startswith("p cnf "):
            fields = line.split()
            lines[index] = f"p cnf {fields[2]} {int(fields[3]) + 1}"
            break
    else:
        raise AssertionError("positive counter parent omitted its DIMACS header")
    lines.append(f"{SPLIT_VARIABLE if positive else -SPLIT_VARIABLE} 0")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--polarity", choices=("positive", "negative"), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(
        render(args.polarity == "positive"), encoding="ascii", newline="\n"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

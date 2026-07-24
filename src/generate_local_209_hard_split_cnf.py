#!/usr/bin/env python3
"""Generate the exhaustive two-unit split of the hard E014 45/44 input."""

from __future__ import annotations

import argparse
from pathlib import Path

from src.generate_local_209_double_classified_hard_cnf import (
    build_instance,
    render as render_base,
)

SPLIT_VARIABLE = 302
SPLIT_NAME = ("exceptional-edge", 0, 5, 7)


def render(positive: bool) -> str:
    cnf, _ = build_instance()
    if cnf.names.get(SPLIT_NAME) != SPLIT_VARIABLE:
        raise AssertionError("E014 hard split variable/name mapping changed")
    lines = render_base().splitlines()
    for index, line in enumerate(lines):
        if line.startswith("p cnf "):
            fields = line.split()
            lines[index] = f"p cnf {fields[2]} {int(fields[3]) + 1}"
            break
    else:
        raise AssertionError("hard E014 CNF omitted its DIMACS header")
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

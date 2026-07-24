#!/usr/bin/env python3
"""Generate the exhaustive two-unit split of the E014 unbalanced53 input."""

from __future__ import annotations

import argparse
from pathlib import Path

from src.generate_local_209_near_cnf import build_instance, render as render_near

SPLIT_VARIABLE = 597
SPLIT_NAME = ("exceptional-edge", 15, 17)


def render(positive: bool) -> str:
    cnf, _ = build_instance("unbalanced53", True, True, None, True)
    if cnf.names.get(SPLIT_NAME) != SPLIT_VARIABLE:
        raise AssertionError("E014 unbalanced53 split variable/name mapping changed")
    lines = render_near("unbalanced53", True, True, None, True).splitlines()
    for index, line in enumerate(lines):
        if line.startswith("p cnf "):
            fields = line.split()
            lines[index] = f"p cnf {fields[2]} {int(fields[3]) + 1}"
            break
    else:
        raise AssertionError("unbalanced53 E014 CNF omitted its DIMACS header")
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

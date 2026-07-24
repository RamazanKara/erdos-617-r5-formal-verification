#!/usr/bin/env python3
"""Refine the unresolved positive variable-7279 E014 unbalanced53 leaf."""

from __future__ import annotations

import argparse
from pathlib import Path

from src.generate_local_209_balanced_counter_refinement_cnf import (
    render as render_parent,
)
from src.generate_local_209_near_cnf import build_instance

SPLIT_NAME = ("counter", "exceptional-edge-count", 62, 18)
SPLIT_VARIABLE = 4947


def render(positive: bool) -> str:
    cnf, _ = build_instance("unbalanced53", True, True, None, True)
    if cnf.names.get(SPLIT_NAME) != SPLIT_VARIABLE:
        raise AssertionError("unbalanced53: variable-4947 counter mapping changed")
    lines = render_parent("unbalanced53", True).splitlines()
    for index, line in enumerate(lines):
        if line.startswith("p cnf "):
            fields = line.split()
            lines[index] = f"p cnf {fields[2]} {int(fields[3]) + 1}"
            break
    else:
        raise AssertionError("unbalanced53 variable-7279-positive parent omitted header")
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

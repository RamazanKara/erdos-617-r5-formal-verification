#!/usr/bin/env python3
"""Secondary balanced-counter split inside the E014 u50 exactly-27 slices."""

from __future__ import annotations

import argparse
from pathlib import Path

from src.generate_local_209_double_classified_u50_full_canonical_cnf import (
    build_instance,
)
from src.generate_local_209_u50_counter_cascade_cnf import render as render_parent

SPLIT_NAME = ("counter", "exceptional-edge-count", 0, 95, 25)
SPLIT_VARIABLE = 6319
TEMPLATES = {"u50_a1": "u4455_a1", "u50_a2": "u4455_a2"}


def render(family: str, positive: bool) -> str:
    if family not in TEMPLATES:
        raise ValueError(f"unknown E014 u50 exact-27 secondary family {family!r}")
    cnf, _ = build_instance(TEMPLATES[family])
    if cnf.names.get(SPLIT_NAME) != SPLIT_VARIABLE:
        raise AssertionError(f"{family}: secondary counter mapping changed")
    lines = render_parent(family, False, 28).splitlines()
    for index, line in enumerate(lines):
        if line.startswith("p cnf "):
            fields = line.split()
            lines[index] = f"p cnf {fields[2]} {int(fields[3]) + 1}"
            break
    else:
        raise AssertionError(f"{family}: exactly-27 parent omitted header")
    lines.append(f"{SPLIT_VARIABLE if positive else -SPLIT_VARIABLE} 0")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=tuple(TEMPLATES), required=True)
    parser.add_argument("--polarity", choices=("positive", "negative"), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(
        render(args.family, args.polarity == "positive"),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

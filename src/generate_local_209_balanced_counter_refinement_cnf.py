#!/usr/bin/env python3
"""Next-threshold refinements for positive direct E014 counter branches."""

from __future__ import annotations

import argparse
from pathlib import Path

from src.generate_local_209_balanced_counter_split_cnf import render as render_parent
from src.generate_local_209_double_classified_hard_cnf import (
    build_instance as build_hard,
)
from src.generate_local_209_double_classified_u50_full_canonical_cnf import (
    build_instance as build_u50,
)
from src.generate_local_209_near_cnf import build_instance as build_near

FAMILIES = {
    "u50_a2": {
        "builder": lambda: build_u50("u4455_a2"),
        "split_name": ("counter", "exceptional-edge-count", 0, 105, 26),
        "split_variable": 6830,
    },
    "hard45_44": {
        "builder": build_hard,
        "split_name": ("counter", "exceptional-edge-count", 0, 95, 24),
        "split_variable": 6081,
    },
    "unbalanced53": {
        "builder": lambda: build_near("unbalanced53", True, True, None, True),
        "split_name": ("counter", "exceptional-edge-count", 105, 28),
        "split_variable": 7279,
    },
}


def render(family: str, positive: bool) -> str:
    if family not in FAMILIES:
        raise ValueError(f"unknown E014 counter refinement {family!r}")
    config = FAMILIES[family]
    cnf, _ = config["builder"]()
    if cnf.names.get(config["split_name"]) != config["split_variable"]:
        raise AssertionError(f"{family}: next counter-threshold mapping changed")
    lines = render_parent(family, True).splitlines()
    for index, line in enumerate(lines):
        if line.startswith("p cnf "):
            fields = line.split()
            lines[index] = f"p cnf {fields[2]} {int(fields[3]) + 1}"
            break
    else:
        raise AssertionError(f"{family}: counter-positive parent omitted header")
    variable = config["split_variable"]
    lines.append(f"{variable if positive else -variable} 0")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=tuple(FAMILIES), required=True)
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

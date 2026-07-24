#!/usr/bin/env python3
"""Balanced cardinality-counter splits for the four open E014 targets."""

from __future__ import annotations

import argparse
from pathlib import Path

from src.generate_local_209_double_classified_hard_cnf import (
    build_instance as build_hard,
)
from src.generate_local_209_double_classified_hard_cnf import render as render_hard
from src.generate_local_209_double_classified_u50_full_canonical_cnf import (
    build_instance as build_u50,
)
from src.generate_local_209_double_classified_u50_full_canonical_cnf import (
    render as render_u50,
)
from src.generate_local_209_near_cnf import build_instance as build_near
from src.generate_local_209_near_cnf import render as render_near

FAMILIES = {
    "u50_a1": {
        "builder": lambda: build_u50("u4455_a1"),
        "renderer": lambda: render_u50("u4455_a1"),
        "split_name": ("counter", "exceptional-edge-count", 0, 105, 25),
        "split_variable": 6829,
    },
    "u50_a2": {
        "builder": lambda: build_u50("u4455_a2"),
        "renderer": lambda: render_u50("u4455_a2"),
        "split_name": ("counter", "exceptional-edge-count", 0, 105, 25),
        "split_variable": 6829,
    },
    "hard45_44": {
        "builder": build_hard,
        "renderer": render_hard,
        "split_name": ("counter", "exceptional-edge-count", 0, 95, 23),
        "split_variable": 6080,
    },
    "unbalanced53": {
        "builder": lambda: build_near("unbalanced53", True, True, None, True),
        "renderer": lambda: render_near("unbalanced53", True, True, None, True),
        "split_name": ("counter", "exceptional-edge-count", 105, 27),
        "split_variable": 7278,
    },
}


def render(family: str, positive: bool) -> str:
    if family not in FAMILIES:
        raise ValueError(f"unknown E014 balanced-counter family {family!r}")
    config = FAMILIES[family]
    cnf, _ = config["builder"]()
    if cnf.names.get(config["split_name"]) != config["split_variable"]:
        raise AssertionError(f"{family}: balanced-counter variable/name mapping changed")
    lines = config["renderer"]().splitlines()
    for index, line in enumerate(lines):
        if line.startswith("p cnf "):
            fields = line.split()
            lines[index] = f"p cnf {fields[2]} {int(fields[3]) + 1}"
            break
    else:
        raise AssertionError(f"{family}: base CNF omitted its DIMACS header")
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

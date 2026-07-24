#!/usr/bin/env python3
"""Split the unresolved E014 u50 counter-positive branches one level deeper."""

from __future__ import annotations

import argparse
from pathlib import Path

from src.generate_local_209_balanced_counter_refinement_cnf import (
    render as render_other_parent,
)
from src.generate_local_209_double_classified_u50_full_canonical_cnf import (
    build_instance,
)
from src.generate_local_209_u50_a1_counter_refinement_cnf import (
    render as render_a1_parent,
)

SPLIT_VARIABLES = {27: 6831, 28: 6832, 29: 6833}
SPLIT_NAME = ("counter", "exceptional-edge-count", 0, 105, 27)
SPLIT_VARIABLE = SPLIT_VARIABLES[27]

FAMILIES = {
    "u50_a1": {
        "builder": lambda: build_instance("u4455_a1"),
        "parent_renderer": lambda: render_a1_parent(True),
    },
    "u50_a2": {
        "builder": lambda: build_instance("u4455_a2"),
        "parent_renderer": lambda: render_other_parent("u50_a2", True),
    },
}


def render(family: str, positive: bool, threshold: int = 27) -> str:
    if family not in FAMILIES:
        raise ValueError(f"unknown E014 u50 counter cascade {family!r}")
    if threshold not in SPLIT_VARIABLES:
        raise ValueError(f"unknown E014 u50 counter threshold {threshold}")
    config = FAMILIES[family]
    cnf, _ = config["builder"]()
    split_name = ("counter", "exceptional-edge-count", 0, 105, threshold)
    split_variable = SPLIT_VARIABLES[threshold]
    if cnf.names.get(split_name) != split_variable:
        raise AssertionError(
            f"{family}: counter-threshold-{threshold} mapping changed"
        )
    parent = (
        config["parent_renderer"]()
        if threshold == 27
        else render(family, True, threshold - 1)
    )
    lines = parent.splitlines()
    for index, line in enumerate(lines):
        if line.startswith("p cnf "):
            fields = line.split()
            lines[index] = f"p cnf {fields[2]} {int(fields[3]) + 1}"
            break
    else:
        raise AssertionError(f"{family}: counter-positive parent omitted header")
    lines.append(f"{split_variable if positive else -split_variable} 0")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=tuple(FAMILIES), required=True)
    parser.add_argument("--polarity", choices=("positive", "negative"), required=True)
    parser.add_argument("--threshold", choices=tuple(SPLIT_VARIABLES), type=int, default=27)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(
        render(args.family, args.polarity == "positive", args.threshold),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

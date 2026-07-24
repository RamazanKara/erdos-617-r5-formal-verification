#!/usr/bin/env python3
"""Generate the exhaustive two-unit split of the hard E014 u4455_a1 input."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_209_double_classified_u50_full_canonical_cnf import (  # noqa: E402
    build_instance,
    render as render_base,
)

TEMPLATE = "u4455_a1"
SPLIT_VARIABLE = 497
SPLIT_NAME = ("exceptional-edge", 0, 15, 17)


def render_template(template: str, positive: bool) -> str:
    cnf, _ = build_instance(template)
    if cnf.names.get(SPLIT_NAME) != SPLIT_VARIABLE:
        raise AssertionError("E014 split variable/name mapping changed")
    lines = render_base(template).splitlines()
    for index, line in enumerate(lines):
        if line.startswith("p cnf "):
            fields = line.split()
            lines[index] = f"p cnf {fields[2]} {int(fields[3]) + 1}"
            break
    else:
        raise AssertionError("base E014 CNF omitted its DIMACS header")
    lines.append(f"{SPLIT_VARIABLE if positive else -SPLIT_VARIABLE} 0")
    return "\n".join(lines) + "\n"


def render(positive: bool) -> str:
    return render_template(TEMPLATE, positive)


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

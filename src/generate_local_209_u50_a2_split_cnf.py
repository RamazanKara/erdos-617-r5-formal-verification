#!/usr/bin/env python3
"""Generate the exhaustive two-unit split of the hard E014 u4455_a2 input."""

from __future__ import annotations

import argparse
from pathlib import Path

from src.generate_local_209_u50_a1_split_cnf import (
    SPLIT_NAME,
    SPLIT_VARIABLE,
    render_template,
)

TEMPLATE = "u4455_a2"


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

#!/usr/bin/env python3
"""Decode an E015 exact fixed-center SAT model to the strict coloring format."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.check_dimacs_model import check_model, read_cnf, read_model  # noqa: E402
from src.generate_local_210_exact_cnf import (  # noqa: E402
    COLORS,
    LOCAL_COUNT,
    POINTS,
    groups_for_profile,
)

CENTER = 25


def primary_edge_variables() -> dict[tuple[int, int, int], int]:
    """Reconstruct the generator's first 1,500 variables independently."""

    variables: dict[tuple[int, int, int], int] = {}
    next_variable = 1
    for color in COLORS:
        for left, right in itertools.combinations(POINTS, 2):
            variables[color, left, right] = next_variable
            next_variable += 1
    if next_variable != 1501:
        raise AssertionError("wrong primary edge-variable count")
    return variables


def decode(profile: str, assignment: tuple[bool, ...]) -> list[list[int]]:
    groups = groups_for_profile(profile)
    point_group = {
        point: color for color, group in groups.items() for point in group
    }
    variables = primary_edge_variables()
    colors = [[-1] * 26 for _ in range(26)]
    local_count = 0

    for left, right in itertools.combinations(POINTS, 2):
        present = [
            color
            for color in COLORS
            if assignment[variables[color, left, right] - 1]
        ]
        if len(present) != 1:
            raise ValueError(
                f"neighbor edge {left} {right} has {len(present)} colors"
            )
        color = present[0]
        colors[left][right] = colors[right][left] = color
        if color not in (point_group[left], point_group[right]):
            local_count += 1

    for point in POINTS:
        color = point_group[point]
        colors[point][CENTER] = colors[CENTER][point] = color

    if local_count != LOCAL_COUNT:
        raise ValueError(
            f"decoded center local count is {local_count}, expected {LOCAL_COUNT}"
        )
    return colors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profile", required=True)
    parser.add_argument("cnf", type=Path)
    parser.add_argument("model", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()

    variables, clauses = read_cnf(args.cnf)
    assignment = read_model(args.model, variables)
    check_model(clauses, assignment)
    colors = decode(args.profile, assignment)

    lines = ["ERDOS617-COLORING-V1 26 5 6"]
    for left in range(26):
        for right in range(left + 1, 26):
            color = colors[left][right]
            if color not in COLORS:
                raise AssertionError("decoder left an edge uncolored")
            lines.append(f"{left} {right} {color}")
    raw = ("\n".join(lines) + "\n").encode("ascii")
    args.output.write_bytes(raw)
    print(
        "LOCAL-210-COLORING-MODEL-DECODE-PASS "
        f"profile={args.profile} variables={variables} clauses={len(clauses)} "
        f"local_count={LOCAL_COUNT} sha256={hashlib.sha256(raw).hexdigest()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

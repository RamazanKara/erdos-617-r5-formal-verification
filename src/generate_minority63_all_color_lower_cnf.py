#!/usr/bin/env python3
"""Add the certified 63-edge lower bound to all remaining colors."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_full_k26_cnf import ORDER, variable
from generate_full_k26_min_degree_branch_cnf import add_at_least_k
from generate_full_k26_minority59_cnf import BASE_CLAUSES, base_clauses
from generate_local_204_cnf import CNF
from generate_minority63_k4_k5_k5_family_cnf import build_formula as build_tertiary
from generate_minority63_min_degree_family_cnf import build_extensions as build_degree

LOWER_BOUND = 63
CASES = {
    "k4_k5_k5_r12": None,
    "k4_k5_r17_d5": ("k4_k5_r17", 5),
    "k5_k5_r16_d4": ("k5_k5_r16", 4),
    "k5_k5_r16_d5": ("k5_k5_r16", 5),
}


def build_prefix(case: str) -> tuple[tuple[CNF, ...], int]:
    if case not in CASES:
        raise ValueError("unknown simultaneous-count exact-63 case")
    degree_case = CASES[case]
    if degree_case is None:
        formula, _metadata = build_tertiary()
        return (formula,), formula.variables
    family, branch, _metadata = build_degree(*degree_case)
    return (family, branch), branch.variables


def build_lower_bounds(starting_variables: int) -> tuple[CNF, dict[str, int]]:
    result = CNF(variables=starting_variables)
    metadata = {"colors": 0, "physical_literals": 0}
    for color in range(1, 5):
        literals = [
            variable(left, right, color)
            for left, right in itertools.combinations(range(ORDER), 2)
        ]
        add_at_least_k(
            result,
            literals,
            LOWER_BOUND,
            ("minority63-all-color-lower", color, LOWER_BOUND),
        )
        metadata["colors"] += 1
        metadata["physical_literals"] += len(literals)
    return result, metadata


def build_extensions(case: str) -> tuple[tuple[CNF, ...], CNF, dict[str, int]]:
    prefix, variables = build_prefix(case)
    lower, metadata = build_lower_bounds(variables)
    return prefix, lower, metadata


def render(case: str, path: Path) -> tuple[int, int, dict[str, int]]:
    prefix, lower, metadata = build_extensions(case)
    clauses = BASE_CLAUSES + sum(len(part.clauses) for part in prefix) + len(
        lower.clauses
    )
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact-63 all-color-lower family, version 1\n")
        stream.write(
            f"c family={case} colors_1_through_4_at_least_63=1 "
            "color_zero_exactly_63=1\n"
        )
        stream.write(f"p cnf {lower.variables} {clauses}\n")
        observed = 0
        for clause in base_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for part in (*prefix, lower):
            for clause in part.clauses:
                stream.write(" ".join(map(str, clause)) + " 0\n")
                observed += 1
    if observed != clauses:
        raise AssertionError("all-color-lower streamed clause count changed")
    return lower.variables, clauses, metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=tuple(CASES), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, metadata = render(args.family, args.output)
    print(
        "MINORITY63-ALL-COLOR-LOWER-CNF-PASS "
        f"family={args.family} variables={variables} clauses={clauses} "
        f"bounded_colors={metadata['colors']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

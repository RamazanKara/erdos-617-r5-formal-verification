#!/usr/bin/env python3
"""Generate the two exact unrestricted component families at color count 63."""

from __future__ import annotations

import argparse
import itertools
import math
from pathlib import Path

from generate_full_k26_cnf import COLORS, ORDER, variable
from generate_full_k26_fixed_minority_graph_cnf import (
    CANONICAL_CLAUSES,
    canonical_remaining_color_clauses,
)
from generate_full_k26_minority59_cnf import BASE_CLAUSES, base_clauses
from generate_local_204_cnf import CNF

BASE_VARIABLES = math.comb(ORDER, 2) * COLORS
CASES = {
    "k4": {"component_size": 4, "residual_edges": 57},
    "k5": {"component_size": 5, "residual_edges": 53},
}


def build_extension(case: str) -> tuple[CNF, dict[str, int]]:
    if case not in CASES:
        raise ValueError("component family must be k4 or k5")
    component_size = CASES[case]["component_size"]
    residual_edges = CASES[case]["residual_edges"]
    component = set(range(component_size))
    residual = tuple(range(component_size, ORDER))
    extension = CNF(variables=BASE_VARIABLES)
    metadata = {
        "positive_component_units": 0,
        "negative_cross_units": 0,
        "residual_physical_edges": math.comb(len(residual), 2),
        "residual_edges": residual_edges,
        "canonical_remaining_colors": CANONICAL_CLAUSES,
    }

    for left, right in itertools.combinations(range(ORDER), 2):
        literal = variable(left, right, 0)
        if left in component and right in component:
            extension.add(literal)
            metadata["positive_component_units"] += 1
        elif (left in component) != (right in component):
            extension.add(-literal)
            metadata["negative_cross_units"] += 1

    residual_literals = [
        variable(left, right, 0)
        for left, right in itertools.combinations(residual, 2)
    ]
    extension.exactly_k(
        residual_literals,
        residual_edges,
        ("minority63-component-family", case, "residual-edges"),
    )
    for clause in canonical_remaining_color_clauses():
        extension.add(*clause)

    if (
        metadata["positive_component_units"] + residual_edges != 63
        or metadata["negative_cross_units"] != component_size * len(residual)
    ):
        raise AssertionError("component-family edge accounting changed")
    return extension, metadata


def expected_counts(case: str) -> tuple[int, int, dict[str, int]]:
    extension, metadata = build_extension(case)
    return extension.variables, BASE_CLAUSES + len(extension.clauses), metadata


def render(case: str, path: Path) -> tuple[int, int, dict[str, int]]:
    extension, metadata = build_extension(case)
    clause_count = BASE_CLAUSES + len(extension.clauses)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(
            "c ERDOS617 exact-63 isolated-component family, version 1\n"
        )
        stream.write(
            f"c family={case} component_size={CASES[case]['component_size']} "
            f"residual_edges={CASES[case]['residual_edges']} "
            "fixed_color_zero=1 canonical_remaining_colors=1\n"
        )
        stream.write(f"p cnf {extension.variables} {clause_count}\n")
        observed = 0
        for clause in base_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for clause in extension.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    return extension.variables, clause_count, metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=tuple(CASES), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, metadata = render(args.family, args.output)
    print(
        "MINORITY63-COMPONENT-FAMILY-CNF-PASS "
        f"family={args.family} variables={variables} clauses={clauses} "
        f"residual_physical_edges={metadata['residual_physical_edges']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

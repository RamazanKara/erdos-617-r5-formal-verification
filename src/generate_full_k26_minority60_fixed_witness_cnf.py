#!/usr/bin/env python3
"""Generate exact-60 branches with one private six-set fixed by relabeling."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_full_k26_cnf import ORDER, variable
from generate_full_k26_min_degree_branch_cnf import add_at_least_k
from generate_full_k26_minority59_cnf import BASE_CLAUSES, base_clauses
from generate_full_k26_minority60_cnf import EDGE_COUNT, MINIMUM_DEGREES
from generate_full_k26_minority60_critical_cnf import critical_extension
from generate_local_204_cnf import CNF

BASE_VARIABLES = 1625
FIXED_WITNESS = tuple(range(6))
FIXED_EDGE = (0, 1)


def build_extensions(degree: int):
    if degree not in MINIMUM_DEGREES:
        raise ValueError("fixed-witness minimum degree must be 3 or 4")

    global_count = CNF(variables=BASE_VARIABLES)
    color_zero = [
        variable(left, right, 0)
        for left, right in itertools.combinations(range(ORDER), 2)
    ]
    global_count.exactly_k(color_zero, EDGE_COUNT, ("minority-edge-count", EDGE_COUNT))

    degree_constraints = CNF(variables=global_count.variables)
    incident_zero = [variable(0, vertex, 0) for vertex in range(1, ORDER)]
    degree_constraints.exactly_k(
        incident_zero, degree, ("selected-minimum-degree", degree)
    )
    for vertex in range(1, ORDER):
        incident = [
            variable(min(vertex, other), max(vertex, other), 0)
            for other in range(ORDER)
            if other != vertex
        ]
        add_at_least_k(
            degree_constraints,
            incident,
            degree,
            ("minority-minimum-degree", degree, vertex),
        )

    orbit = CNF(variables=degree_constraints.variables)
    orbit.add(variable(*FIXED_EDGE, 0))
    for left, right in itertools.combinations(FIXED_WITNESS, 2):
        if (left, right) != FIXED_EDGE:
            orbit.add(-variable(left, right, 0))
    # Edge (0,2) is not color zero, and colors 1,...,4 are interchangeable.
    orbit.add(variable(0, 2, 1))

    critical, metadata = critical_extension(orbit.variables)
    return global_count, degree_constraints, orbit, critical, metadata


def expected_counts(degree: int) -> tuple[int, int, int]:
    extensions = build_extensions(degree)
    formula_parts = extensions[:4]
    clauses = BASE_CLAUSES + sum(len(part.clauses) for part in formula_parts)
    return formula_parts[-1].variables, clauses, len(formula_parts[2].clauses)


def render(degree: int, path: Path) -> tuple[int, int]:
    global_count, degrees, orbit, critical, metadata = build_extensions(degree)
    parts = (global_count, degrees, orbit, critical)
    variables = critical.variables
    clause_count = BASE_CLAUSES + sum(len(part.clauses) for part in parts)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(
            "c ERDOS617 exact unrestricted K26 minority-60 fixed-witness branch, "
            "version 1\n"
        )
        stream.write(
            f"c color_zero_edges=60 minimum_degree={degree} "
            "private_witness=0,1,2,3,4,5 remaining_color_fix=1\n"
        )
        stream.write(f"p cnf {variables} {clause_count}\n")
        observed = 0
        for clause in base_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for part in parts:
            for clause in part.clauses:
                stream.write(" ".join(map(str, clause)) + " 0\n")
                observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    if len(orbit.clauses) != 16 or metadata["conditional_cardinalities"] != 325:
        raise AssertionError("fixed-witness branch dimensions changed")
    return variables, clause_count


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--minimum-degree", type=int, choices=MINIMUM_DEGREES, required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.minimum_degree, args.output)
    print(
        "FULL-K26-MINORITY60-FIXED-WITNESS-CNF-PASS "
        f"minimum_degree={args.minimum_degree} variables={variables} clauses={clauses}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

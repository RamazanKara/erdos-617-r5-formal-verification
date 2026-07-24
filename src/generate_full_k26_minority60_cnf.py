#!/usr/bin/env python3
"""Generate the two exhaustive exact-60 minority-color full K26 branches."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_full_k26_cnf import (
    ORDER,
    clauses as unrestricted_clauses,
    expected_counts as unrestricted_counts,
    variable,
)
from generate_full_k26_min_degree_branch_cnf import branch_extension
from generate_local_204_cnf import CNF

EDGE_COUNT = 60
MINIMUM_DEGREES = (3, 4)
BASE_VARIABLES, BASE_CLAUSES = unrestricted_counts()


def build_extensions(degree: int) -> tuple[CNF, CNF]:
    if degree not in MINIMUM_DEGREES:
        raise ValueError("exact-60 minimum degree must be 3 or 4")
    cardinality = CNF(variables=BASE_VARIABLES)
    color_zero = [
        variable(left, right, 0)
        for left, right in itertools.combinations(range(ORDER), 2)
    ]
    cardinality.exactly_k(color_zero, EDGE_COUNT, ("minority-edge-count", EDGE_COUNT))
    branch = branch_extension(degree, cardinality.variables)
    return cardinality, branch


def expected_counts(degree: int) -> tuple[int, int, int, int]:
    cardinality, branch = build_extensions(degree)
    clauses = BASE_CLAUSES + len(cardinality.clauses) + len(branch.clauses)
    return (
        branch.variables,
        clauses,
        len(cardinality.clauses),
        len(branch.clauses),
    )


def render(degree: int, path: Path) -> tuple[int, int]:
    cardinality, branch = build_extensions(degree)
    variables = branch.variables
    clause_count = BASE_CLAUSES + len(cardinality.clauses) + len(branch.clauses)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(
            "c ERDOS617 exact unrestricted K26 minority-60 branch, version 1\n"
        )
        stream.write(
            f"c color_zero_edges={EDGE_COUNT} minimum_degree={degree} "
            "sorted_spokes=1\n"
        )
        stream.write(f"p cnf {variables} {clause_count}\n")
        observed = 0
        for clause in unrestricted_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for clause in cardinality.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for clause in branch.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    return variables, clause_count


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--minimum-degree", type=int, choices=MINIMUM_DEGREES, required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.minimum_degree, args.output)
    print(
        "FULL-K26-MINORITY60-CNF-PASS "
        f"minimum_degree={args.minimum_degree} variables={variables} clauses={clauses}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

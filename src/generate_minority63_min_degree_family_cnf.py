#!/usr/bin/env python3
"""Split the two unresolved refined exact-63 families by residual degree."""

from __future__ import annotations

import argparse
from pathlib import Path

from generate_full_k26_cnf import variable
from generate_full_k26_min_degree_branch_cnf import add_at_least_k
from generate_full_k26_minority59_cnf import BASE_CLAUSES, base_clauses
from generate_local_204_cnf import CNF
from generate_minority63_refined_family_cnf import build_formula

CASES = {
    "k4_k5_r17": tuple(range(9, 26)),
    "k5_k5_r16": tuple(range(10, 26)),
}
MINIMUM_DEGREES = (4, 5)


def build_degree_branch(
    case: str, degree: int, starting_variables: int
) -> tuple[CNF, dict[str, int]]:
    if case not in CASES or degree not in MINIMUM_DEGREES:
        raise ValueError("unsupported exact-63 residual degree branch")
    residual = CASES[case]
    selected = residual[0]
    neighbors = set(residual[1 : 1 + degree])
    result = CNF(variables=starting_variables)
    metadata = {
        "minimum_degree_constraints": 0,
        "fixed_positive_spokes": 0,
        "fixed_negative_spokes": 0,
    }
    if degree == 5:
        for point in residual:
            add_at_least_k(
                result,
                [
                    variable(min(point, other), max(point, other), 0)
                    for other in residual
                    if other != point
                ],
                degree,
                ("minority63-refined-degree-branch", case, degree, point),
            )
            metadata["minimum_degree_constraints"] += 1
    for other in residual[1:]:
        literal = variable(selected, other, 0)
        if other in neighbors:
            result.add(literal)
            metadata["fixed_positive_spokes"] += 1
        else:
            result.add(-literal)
            metadata["fixed_negative_spokes"] += 1
    if (
        metadata["fixed_positive_spokes"] != degree
        or metadata["fixed_negative_spokes"] != len(residual) - 1 - degree
    ):
        raise AssertionError("residual degree representative changed")
    return result, metadata


def build_extensions(case: str, degree: int) -> tuple[CNF, CNF, dict[str, int]]:
    family, _family_metadata = build_formula(case)
    branch, metadata = build_degree_branch(case, degree, family.variables)
    return family, branch, metadata


def render(case: str, degree: int, path: Path) -> tuple[int, int, dict[str, int]]:
    family, branch, metadata = build_extensions(case, degree)
    clause_count = BASE_CLAUSES + len(family.clauses) + len(branch.clauses)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact-63 refined minimum-degree family, version 1\n")
        stream.write(
            f"c family={case} residual_minimum_degree={degree} "
            "fixed_minimum_degree_vertex=1\n"
        )
        stream.write(f"p cnf {branch.variables} {clause_count}\n")
        observed = 0
        for clause in base_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for extension in (family, branch):
            for clause in extension.clauses:
                stream.write(" ".join(map(str, clause)) + " 0\n")
                observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    return branch.variables, clause_count, metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=tuple(CASES), required=True)
    parser.add_argument("--degree", type=int, choices=MINIMUM_DEGREES, required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, metadata = render(args.family, args.degree, args.output)
    print(
        "MINORITY63-MIN-DEGREE-FAMILY-CNF-PASS "
        f"family={args.family} degree={args.degree} "
        f"variables={variables} clauses={clauses} "
        f"fixed_spokes={metadata['fixed_positive_spokes']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

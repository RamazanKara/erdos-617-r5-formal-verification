#!/usr/bin/env python3
"""Strengthen the exact-63 component families by inherited criticality."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_full_k26_cnf import ORDER, variable
from generate_full_k26_min_degree_branch_cnf import add_at_least_k
from generate_full_k26_minority59_cnf import BASE_CLAUSES, base_clauses
from generate_full_k26_minority60_critical_cnf import add_conditional_exactly_k
from generate_local_204_cnf import CNF
from generate_minority63_component_family_cnf import CASES, build_extension

MINIMUM_RESIDUAL_DEGREE = {"k4": 3, "k5": 4}
ADDITIONAL_PRIVATE_POINTS = 3


def build_strengthening(case: str, starting_variables: int) -> tuple[CNF, dict[str, int]]:
    if case not in CASES:
        raise ValueError("component family must be k4 or k5")
    residual = tuple(range(CASES[case]["component_size"], ORDER))
    minimum_degree = MINIMUM_RESIDUAL_DEGREE[case]
    result = CNF(variables=starting_variables)
    metadata = {
        "minimum_degree_constraints": 0,
        "critical_edges": 0,
        "critical_selectors": 0,
        "endpoint_nonedge_clauses": 0,
        "selected_pair_nonedge_clauses": 0,
    }

    for point in residual:
        incident = [
            variable(min(point, other), max(point, other), 0)
            for other in residual
            if other != point
        ]
        add_at_least_k(
            result,
            incident,
            minimum_degree,
            ("minority63-residual-minimum-degree", case, point),
        )
        metadata["minimum_degree_constraints"] += 1

    for left, right in itertools.combinations(residual, 2):
        gate = variable(left, right, 0)
        available = tuple(point for point in residual if point not in (left, right))
        selected = {
            point: result.variable(
                "minority63-private-independent-five", case, left, right, point
            )
            for point in available
        }
        metadata["critical_edges"] += 1
        metadata["critical_selectors"] += len(selected)
        add_conditional_exactly_k(
            result,
            gate,
            [selected[point] for point in available],
            ADDITIONAL_PRIVATE_POINTS,
            ("minority63-private-independent-five", case, left, right),
        )
        for point in available:
            choice = selected[point]
            result.add(
                -gate,
                -choice,
                -variable(min(left, point), max(left, point), 0),
            )
            result.add(
                -gate,
                -choice,
                -variable(min(right, point), max(right, point), 0),
            )
            metadata["endpoint_nonedge_clauses"] += 2
        for first, second in itertools.combinations(available, 2):
            result.add(
                -gate,
                -selected[first],
                -selected[second],
                -variable(first, second, 0),
            )
            metadata["selected_pair_nonedge_clauses"] += 1
    return result, metadata


def build_extensions(case: str) -> tuple[CNF, CNF, dict[str, int]]:
    family, _family_metadata = build_extension(case)
    strengthening, metadata = build_strengthening(case, family.variables)
    return family, strengthening, metadata


def render(case: str, path: Path) -> tuple[int, int, dict[str, int]]:
    family, strengthening, metadata = build_extensions(case)
    clause_count = BASE_CLAUSES + len(family.clauses) + len(strengthening.clauses)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(
            "c ERDOS617 exact-63 critical isolated-component family, version 1\n"
        )
        stream.write(
            f"c family={case} component_size={CASES[case]['component_size']} "
            f"residual_edges={CASES[case]['residual_edges']} "
            f"minimum_residual_degree={MINIMUM_RESIDUAL_DEGREE[case]} "
            "private_independent_five_per_residual_edge=1\n"
        )
        stream.write(f"p cnf {strengthening.variables} {clause_count}\n")
        observed = 0
        for clause in base_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for extension in (family, strengthening):
            for clause in extension.clauses:
                stream.write(" ".join(map(str, clause)) + " 0\n")
                observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    return strengthening.variables, clause_count, metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=tuple(CASES), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, metadata = render(args.family, args.output)
    print(
        "MINORITY63-CRITICAL-COMPONENT-FAMILY-CNF-PASS "
        f"family={args.family} variables={variables} clauses={clauses} "
        f"critical_edges={metadata['critical_edges']} "
        f"critical_selectors={metadata['critical_selectors']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

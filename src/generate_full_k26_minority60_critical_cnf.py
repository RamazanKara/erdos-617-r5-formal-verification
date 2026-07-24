#!/usr/bin/env python3
"""Generate exact-60 branches with mandatory private six-set witnesses."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_full_k26_cnf import ORDER, clauses as unrestricted_clauses, variable
from generate_full_k26_minority60_cnf import (
    BASE_CLAUSES,
    MINIMUM_DEGREES,
    build_extensions as build_minority60_extensions,
)
from generate_local_204_cnf import CNF

WITNESS_ADDITIONAL_POINTS = 4


def add_conditional_exactly_k(
    cnf: CNF,
    gate: int,
    literals: list[int],
    bound: int,
    label: tuple[object, ...],
) -> None:
    """Force literals to total bound if gate, and zero if not gate."""

    if not 0 <= bound <= len(literals):
        raise ValueError("conditional cardinality bound outside range")
    off = [cnf.variable("conditional-off", *label, index) for index in range(bound)]
    for disabled in off:
        cnf.add(-disabled, -gate)
        cnf.add(gate, disabled)
    for literal in literals:
        cnf.add(-literal, gate)
    cnf.exactly_k(literals + off, bound, ("conditional-count", *label))


def critical_extension(starting_variables: int) -> tuple[CNF, dict[str, int]]:
    cnf = CNF(variables=starting_variables)
    selector_variables = 0
    conditional_cardinalities = 0
    endpoint_nonedge_clauses = 0
    selected_pair_nonedge_clauses = 0

    for left, right in itertools.combinations(range(ORDER), 2):
        gate = variable(left, right, 0)
        available = tuple(
            point for point in range(ORDER) if point not in (left, right)
        )
        selected = {
            point: cnf.variable("private-six-set", left, right, point)
            for point in available
        }
        selector_variables += len(selected)
        add_conditional_exactly_k(
            cnf,
            gate,
            [selected[point] for point in available],
            WITNESS_ADDITIONAL_POINTS,
            ("private-six-set", left, right),
        )
        conditional_cardinalities += 1

        for point in available:
            choice = selected[point]
            cnf.add(
                -gate,
                -choice,
                -variable(min(left, point), max(left, point), 0),
            )
            cnf.add(
                -gate,
                -choice,
                -variable(min(right, point), max(right, point), 0),
            )
            endpoint_nonedge_clauses += 2
        for first, second in itertools.combinations(available, 2):
            cnf.add(
                -gate,
                -selected[first],
                -selected[second],
                -variable(first, second, 0),
            )
            selected_pair_nonedge_clauses += 1

    return cnf, {
        "selector_variables": selector_variables,
        "conditional_cardinalities": conditional_cardinalities,
        "endpoint_nonedge_clauses": endpoint_nonedge_clauses,
        "selected_pair_nonedge_clauses": selected_pair_nonedge_clauses,
    }


def build_extensions(degree: int):
    cardinality, branch = build_minority60_extensions(degree)
    critical, metadata = critical_extension(branch.variables)
    return cardinality, branch, critical, metadata


def expected_counts(degree: int) -> tuple[int, int, int]:
    cardinality, branch, critical, _ = build_extensions(degree)
    clauses = (
        BASE_CLAUSES
        + len(cardinality.clauses)
        + len(branch.clauses)
        + len(critical.clauses)
    )
    return critical.variables, clauses, len(critical.clauses)


def render(degree: int, path: Path) -> tuple[int, int]:
    cardinality, branch, critical, metadata = build_extensions(degree)
    variables = critical.variables
    clause_count = (
        BASE_CLAUSES
        + len(cardinality.clauses)
        + len(branch.clauses)
        + len(critical.clauses)
    )
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(
            "c ERDOS617 exact unrestricted K26 minority-60 critical branch, "
            "version 1\n"
        )
        stream.write(
            f"c color_zero_edges=60 minimum_degree={degree} "
            "private_six_set_per_edge=1\n"
        )
        stream.write(f"p cnf {variables} {clause_count}\n")
        observed = 0
        for clause in unrestricted_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for extension in (cardinality, branch, critical):
            for clause in extension.clauses:
                stream.write(" ".join(map(str, clause)) + " 0\n")
                observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    if metadata != {
        "selector_variables": 7_800,
        "conditional_cardinalities": 325,
        "endpoint_nonedge_clauses": 15_600,
        "selected_pair_nonedge_clauses": 89_700,
    }:
        raise AssertionError("private-witness dimensions changed")
    return variables, clause_count


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--minimum-degree", type=int, choices=MINIMUM_DEGREES, required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.minimum_degree, args.output)
    print(
        "FULL-K26-MINORITY60-CRITICAL-CNF-PASS "
        f"minimum_degree={args.minimum_degree} variables={variables} clauses={clauses}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

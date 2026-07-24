#!/usr/bin/env python3
"""Generate graph-only exact-60 critical minority-color branches on 26 points."""

from __future__ import annotations

import argparse
import itertools
import math
from pathlib import Path

from generate_full_k26_cnf import ORDER, WITNESS_SIZE, edge_index
from generate_full_k26_min_degree_branch_cnf import add_at_least_k
from generate_full_k26_minority60_critical_cnf import add_conditional_exactly_k
from generate_local_204_cnf import CNF

EDGE_COUNT = 60
MINIMUM_DEGREES = (3, 4)
PHYSICAL_VARIABLES = math.comb(ORDER, 2)
FIXED_SIX_SET = tuple(range(WITNESS_SIZE))
FIXED_EDGE = (0, 1)


def graph_variable(left: int, right: int) -> int:
    """Dense one-based adjacency variable for an unordered edge of K_26."""

    if left > right:
        left, right = right, left
    return edge_index(left, right) + 1


def graph_base_clauses():
    """Forbid both a clique and an independent set on every six-set."""

    for subset in itertools.combinations(range(ORDER), WITNESS_SIZE):
        edges = [graph_variable(left, right) for left, right in itertools.combinations(subset, 2)]
        yield edges
        yield [-literal for literal in edges]


BASE_CLAUSES = 2 * math.comb(ORDER, WITNESS_SIZE)


def critical_extension(starting_variables: int) -> tuple[CNF, dict[str, int]]:
    """Require every present edge to have a private independent six-set."""

    cnf = CNF(variables=starting_variables)
    metadata = {
        "selector_variables": 0,
        "conditional_cardinalities": 0,
        "endpoint_nonedge_clauses": 0,
        "selected_pair_nonedge_clauses": 0,
    }
    for left, right in itertools.combinations(range(ORDER), 2):
        gate = graph_variable(left, right)
        available = tuple(point for point in range(ORDER) if point not in (left, right))
        selected = {
            point: cnf.variable("private-six-set", left, right, point)
            for point in available
        }
        metadata["selector_variables"] += len(selected)
        add_conditional_exactly_k(
            cnf,
            gate,
            [selected[point] for point in available],
            4,
            ("graph-private-six-set", left, right),
        )
        metadata["conditional_cardinalities"] += 1

        for point in available:
            choice = selected[point]
            cnf.add(-gate, -choice, -graph_variable(left, point))
            cnf.add(-gate, -choice, -graph_variable(right, point))
            metadata["endpoint_nonedge_clauses"] += 2
        for first, second in itertools.combinations(available, 2):
            cnf.add(
                -gate,
                -selected[first],
                -selected[second],
                -graph_variable(first, second),
            )
            metadata["selected_pair_nonedge_clauses"] += 1
    return cnf, metadata


def build_extensions(degree: int):
    if degree not in MINIMUM_DEGREES:
        raise ValueError("minimum degree must be three or four")

    cardinality = CNF(variables=PHYSICAL_VARIABLES)
    cardinality.exactly_k(
        [graph_variable(left, right) for left, right in itertools.combinations(range(ORDER), 2)],
        EDGE_COUNT,
        ("graph-edge-count", EDGE_COUNT),
    )

    degrees = CNF(variables=cardinality.variables)
    degrees.exactly_k(
        [graph_variable(0, vertex) for vertex in range(1, ORDER)],
        degree,
        ("selected-minimum-degree", degree),
    )
    for vertex in range(1, ORDER):
        incident = [
            graph_variable(vertex, other)
            for other in range(ORDER)
            if other != vertex
        ]
        add_at_least_k(
            degrees,
            incident,
            degree,
            ("graph-minimum-degree", degree, vertex),
        )

    orbit = CNF(variables=degrees.variables)
    orbit.add(graph_variable(*FIXED_EDGE))
    for left, right in itertools.combinations(FIXED_SIX_SET, 2):
        if (left, right) != FIXED_EDGE:
            orbit.add(-graph_variable(left, right))

    critical, metadata = critical_extension(orbit.variables)
    # Name the particular witness used to label vertices 2,...,5.  Other
    # witnesses for edge (0,1) remain immaterial and need not be forbidden.
    for point in range(ORDER):
        if point in FIXED_EDGE:
            continue
        selector = critical.names["private-six-set", 0, 1, point]
        critical.add(selector if point in (2, 3, 4, 5) else -selector)

    return cardinality, degrees, orbit, critical, metadata


def expected_counts(degree: int) -> tuple[int, int]:
    parts = build_extensions(degree)
    formula_parts = parts[:4]
    return (
        formula_parts[-1].variables,
        BASE_CLAUSES + sum(len(part.clauses) for part in formula_parts),
    )


def render(degree: int, path: Path) -> tuple[int, int]:
    cardinality, degrees, orbit, critical, metadata = build_extensions(degree)
    parts = (cardinality, degrees, orbit, critical)
    variables = critical.variables
    clause_count = BASE_CLAUSES + sum(len(part.clauses) for part in parts)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact-60 critical minority graph, version 1\n")
        stream.write(
            f"c edges=60 minimum_degree={degree} fixed_private_witness=0,1,2,3,4,5\n"
        )
        stream.write(f"p cnf {variables} {clause_count}\n")
        observed = 0
        for clause in graph_base_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for part in parts:
            for clause in part.clauses:
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
        raise AssertionError("critical graph dimensions changed")
    return variables, clause_count


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--minimum-degree", type=int, choices=MINIMUM_DEGREES, required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.minimum_degree, args.output)
    print(
        "MINORITY60-CRITICAL-GRAPH-CNF-PASS "
        f"minimum_degree={args.minimum_degree} variables={variables} clauses={clauses}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

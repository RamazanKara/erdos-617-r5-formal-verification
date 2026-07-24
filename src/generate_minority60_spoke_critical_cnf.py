#!/usr/bin/env python3
"""Necessary exact-60 graph branches retaining only spoke criticality."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_full_k26_cnf import ORDER
from generate_full_k26_min_degree_branch_cnf import add_at_least_k
from generate_local_204_cnf import CNF
from generate_minority60_critical_graph_cnf import (
    BASE_CLAUSES,
    EDGE_COUNT,
    PHYSICAL_VARIABLES,
    graph_base_clauses,
    graph_variable,
)

BRANCHES = {
    "degree3": (3, (1, 6, 7)),
    "degree4-nonclique": (4, (1, 6, 7, 8)),
    "degree4-clique-leak": (4, (1, 6, 7, 8)),
}
FIXED_WITNESS = (0, 1, 2, 3, 4, 5)


def private_spoke_extension(starting_variables: int, neighbors: tuple[int, ...]) -> CNF:
    """Require private six-sets for the known present spokes other than (0,1)."""

    cnf = CNF(variables=starting_variables)
    for neighbor in neighbors:
        if neighbor == 1:
            continue
        available = [point for point in range(1, ORDER) if point != neighbor]
        selected = [
            cnf.variable("spoke-private-six-set", neighbor, point)
            for point in available
        ]
        cnf.exactly_k(selected, 4, ("spoke-private-count", neighbor))
        choice = dict(zip(available, selected, strict=True))
        for point in available:
            cnf.add(-choice[point], -graph_variable(0, point))
            cnf.add(-choice[point], -graph_variable(neighbor, point))
        for first, second in itertools.combinations(available, 2):
            cnf.add(
                -choice[first],
                -choice[second],
                -graph_variable(first, second),
            )
    return cnf


def build_extensions(branch: str):
    if branch not in BRANCHES:
        raise ValueError("unknown spoke-critical branch")
    degree, neighbors = BRANCHES[branch]

    cardinality = CNF(variables=PHYSICAL_VARIABLES)
    all_edges = [
        graph_variable(left, right)
        for left, right in itertools.combinations(range(ORDER), 2)
    ]
    cardinality.exactly_k(all_edges, EDGE_COUNT, ("graph-edge-count", EDGE_COUNT))

    degrees = CNF(variables=cardinality.variables)
    incident_zero = [graph_variable(0, vertex) for vertex in range(1, ORDER)]
    degrees.exactly_k(
        incident_zero,
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
    for left, right in itertools.combinations(FIXED_WITNESS, 2):
        literal = graph_variable(left, right)
        orbit.add(literal if (left, right) == (0, 1) else -literal)
    for neighbor in neighbors:
        orbit.add(graph_variable(0, neighbor))

    if branch == "degree4-nonclique":
        orbit.add(-graph_variable(1, 6))
    elif branch == "degree4-clique-leak":
        for left, right in itertools.combinations(neighbors, 2):
            orbit.add(graph_variable(left, right))
        orbit.add(-graph_variable(0, 9))
        orbit.add(graph_variable(1, 9))

    spoke_critical = private_spoke_extension(orbit.variables, neighbors)
    return cardinality, degrees, orbit, spoke_critical


def expected_counts(branch: str) -> tuple[int, int]:
    parts = build_extensions(branch)
    return parts[-1].variables, BASE_CLAUSES + sum(len(part.clauses) for part in parts)


def render(branch: str, path: Path) -> tuple[int, int]:
    parts = build_extensions(branch)
    variables = parts[-1].variables
    clause_count = BASE_CLAUSES + sum(len(part.clauses) for part in parts)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact-60 spoke-critical graph relaxation, version 1\n")
        stream.write(f"c branch={branch} critical_spokes_only=1\n")
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
    return variables, clause_count


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", choices=tuple(BRANCHES), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.branch, args.output)
    print(
        "MINORITY60-SPOKE-CRITICAL-CNF-PASS "
        f"branch={args.branch} variables={variables} clauses={clauses}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

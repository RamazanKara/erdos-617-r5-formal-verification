#!/usr/bin/env python3
"""Generate the graph-only CNF for the finite r=5 Brooks substitute."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_local_204_cnf import CNF

ORDER = 26
DEGREE = 5
SET_SIZE = 6
FIXED_NEIGHBORS = tuple(range(1, DEGREE + 1))


def edge_pairs():
    return itertools.combinations(range(ORDER), 2)


def edge_variable(cnf: CNF, left: int, right: int) -> int:
    if left == right:
        raise ValueError("a simple-graph edge needs distinct endpoints")
    if not 0 <= left < ORDER or not 0 <= right < ORDER:
        raise ValueError("edge endpoint outside the graph")
    left, right = sorted((left, right))
    return cnf.variable("edge", left, right)


def build_instance() -> CNF:
    cnf = CNF()

    # Allocate all primary variables first, in lexicographic edge order.
    for left, right in edge_pairs():
        edge_variable(cnf, left, right)

    # Exact degree five at every labelled vertex.
    for vertex in range(ORDER):
        incident = [
            edge_variable(cnf, vertex, other)
            for other in range(ORDER)
            if other != vertex
        ]
        cnf.exactly_k(incident, DEGREE, ("degree", vertex))

    # Safe orbit: vertex zero has precisely neighbors one through five.
    for other in range(1, ORDER):
        variable = edge_variable(cnf, 0, other)
        cnf.add(variable if other in FIXED_NEIGHBORS else -variable)

    # Every six-set contains an edge and a nonedge.
    for vertices in itertools.combinations(range(ORDER), SET_SIZE):
        induced = [
            edge_variable(cnf, left, right)
            for left, right in itertools.combinations(vertices, 2)
        ]
        cnf.add(*induced)
        cnf.add(*(-variable for variable in induced))

    return cnf


def expected_counts() -> tuple[int, int, int]:
    cnf = build_instance()
    primary = ORDER * (ORDER - 1) // 2
    return cnf.variables, len(cnf.clauses), primary


def render(path: Path) -> tuple[int, int]:
    cnf = build_instance()
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 finite r=5 Brooks substitute, version 1\n")
        stream.write(
            "c simple graph order=26 degree=5 alpha<=5 omega<=5 "
            "neighbors(0)=1,2,3,4,5\n"
        )
        stream.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    return cnf.variables, len(cnf.clauses)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.output)
    print(
        "R5-FIVE-REGULAR-BROOKS-CNF-PASS "
        f"order={ORDER} degree={DEGREE} variables={variables} clauses={clauses} "
        f"six_sets={len(tuple(itertools.combinations(range(ORDER), SET_SIZE)))}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

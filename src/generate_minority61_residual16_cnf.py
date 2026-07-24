#!/usr/bin/env python3
"""Generate the 16-vertex minimum-degree-five exact-61 residual family."""

from __future__ import annotations

import argparse
import itertools
import math
from pathlib import Path

from generate_full_k26_min_degree_branch_cnf import add_at_least_k
from generate_full_k26_minority60_critical_cnf import add_conditional_exactly_k
from generate_local_204_cnf import CNF

ORDER = 16
EDGE_COUNT = 41
MINIMUM_DEGREE = 5
PHYSICAL_VARIABLES = math.comb(ORDER, 2)
FIXED_EDGE = (0, 1)
FIXED_PRIVATE_SET = (0, 1, 2, 3)


def edge_index(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < ORDER:
        raise ValueError("residual edge endpoints out of range")
    return left * (2 * ORDER - left - 1) // 2 + right - left - 1


def variable(left: int, right: int) -> int:
    return edge_index(left, right) + 1


def build_formula() -> tuple[CNF, dict[str, int]]:
    cnf = CNF(variables=PHYSICAL_VARIABLES)
    metadata = {
        "independent_four_clauses": 0,
        "clique_six_clauses": 0,
        "minimum_degree_constraints": 0,
        "critical_selectors": 0,
        "conditional_cardinalities": 0,
        "endpoint_nonedge_clauses": 0,
        "selected_pair_nonedge_clauses": 0,
        "fixed_witness_units": 0,
    }

    for subset in itertools.combinations(range(ORDER), 4):
        cnf.add(
            *[
                variable(left, right)
                for left, right in itertools.combinations(subset, 2)
            ]
        )
        metadata["independent_four_clauses"] += 1

    for subset in itertools.combinations(range(ORDER), 6):
        cnf.add(
            *[
                -variable(left, right)
                for left, right in itertools.combinations(subset, 2)
            ]
        )
        metadata["clique_six_clauses"] += 1

    all_edges = [
        variable(left, right)
        for left, right in itertools.combinations(range(ORDER), 2)
    ]
    cnf.exactly_k(all_edges, EDGE_COUNT, ("minority61-residual16-edges", EDGE_COUNT))

    for vertex in range(ORDER):
        incident = [variable(vertex, other) for other in range(ORDER) if other != vertex]
        add_at_least_k(
            cnf,
            incident,
            MINIMUM_DEGREE,
            ("minority61-residual16-minimum-degree", vertex),
        )
        metadata["minimum_degree_constraints"] += 1

    for left, right in itertools.combinations(range(ORDER), 2):
        gate = variable(left, right)
        available = tuple(point for point in range(ORDER) if point not in (left, right))
        selected = {
            point: cnf.variable("private-independent-four", left, right, point)
            for point in available
        }
        metadata["critical_selectors"] += len(selected)
        add_conditional_exactly_k(
            cnf,
            gate,
            [selected[point] for point in available],
            2,
            ("minority61-residual16-private-four", left, right),
        )
        metadata["conditional_cardinalities"] += 1
        for point in available:
            choice = selected[point]
            cnf.add(-gate, -choice, -variable(left, point))
            cnf.add(-gate, -choice, -variable(right, point))
            metadata["endpoint_nonedge_clauses"] += 2
        for first, second in itertools.combinations(available, 2):
            cnf.add(
                -gate,
                -selected[first],
                -selected[second],
                -variable(first, second),
            )
            metadata["selected_pair_nonedge_clauses"] += 1

    cnf.add(variable(*FIXED_EDGE))
    metadata["fixed_witness_units"] += 1
    for left, right in itertools.combinations(FIXED_PRIVATE_SET, 2):
        if (left, right) != FIXED_EDGE:
            cnf.add(-variable(left, right))
            metadata["fixed_witness_units"] += 1
    for point in range(ORDER):
        if point in FIXED_EDGE:
            continue
        selector = cnf.names["private-independent-four", 0, 1, point]
        cnf.add(selector if point in (2, 3) else -selector)
        metadata["fixed_witness_units"] += 1

    return cnf, metadata


def render(path: Path) -> tuple[int, int, dict[str, int]]:
    cnf, metadata = build_formula()
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact-61 residual16 critical graph, version 1\n")
        stream.write("c order=16 edges=41 minimum_degree=5 fixed_private_four=0,1,2,3\n")
        stream.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    return cnf.variables, len(cnf.clauses), metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, metadata = render(args.output)
    print(
        "MINORITY61-RESIDUAL16-CNF-PASS "
        f"variables={variables} clauses={clauses} "
        f"critical_selectors={metadata['critical_selectors']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

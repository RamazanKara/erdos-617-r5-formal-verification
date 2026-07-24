#!/usr/bin/env python3
"""Generate the graph-only exact-63 final Q16 critical-core obligation."""

from __future__ import annotations

import argparse
import itertools
import math
from pathlib import Path

from generate_full_k26_min_degree_branch_cnf import add_at_least_k
from generate_local_204_cnf import CNF

ORDER = 16
EDGE_COUNT = 43
MINIMUM_DEGREE = 5
AUXILIARY_COLORS = 5
PHYSICAL_EDGES = tuple(itertools.combinations(range(ORDER), 2))


def variable(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < ORDER:
        raise ValueError("Q16 edge endpoints out of range")
    return left * (2 * ORDER - left - 1) // 2 + right - left


def build_formula() -> tuple[CNF, dict[str, int]]:
    result = CNF(variables=math.comb(ORDER, 2))
    metadata = {
        "independent_four_clauses": 0,
        "clique_six_clauses": 0,
        "minimum_degree_constraints": 0,
        "fixed_positive_spokes": 0,
        "fixed_negative_spokes": 0,
        "critical_edges": 0,
        "critical_selectors": 0,
        "critical_existence_clauses": 0,
        "critical_nonedge_clauses": 0,
        "deleted_vertex_colorings": 0,
        "color_variables": 0,
        "one_hot_at_least_clauses": 0,
        "one_hot_at_most_clauses": 0,
        "proper_edge_clauses": 0,
    }

    result.exactly_k(
        [variable(left, right) for left, right in PHYSICAL_EDGES],
        EDGE_COUNT,
        ("minority63-q16-graph", "edges", EDGE_COUNT),
    )
    for point in range(ORDER):
        add_at_least_k(
            result,
            [variable(point, other) for other in range(ORDER) if other != point],
            MINIMUM_DEGREE,
            ("minority63-q16-graph", "minimum-degree", point),
        )
        metadata["minimum_degree_constraints"] += 1
    for other in range(1, ORDER):
        if other <= MINIMUM_DEGREE:
            result.add(variable(0, other))
            metadata["fixed_positive_spokes"] += 1
        else:
            result.add(-variable(0, other))
            metadata["fixed_negative_spokes"] += 1

    for subset in itertools.combinations(range(ORDER), 4):
        result.add(*[variable(left, right) for left, right in itertools.combinations(subset, 2)])
        metadata["independent_four_clauses"] += 1
    for subset in itertools.combinations(range(ORDER), 6):
        result.add(*[-variable(left, right) for left, right in itertools.combinations(subset, 2)])
        metadata["clique_six_clauses"] += 1

    for left, right in PHYSICAL_EDGES:
        edge = variable(left, right)
        available = tuple(point for point in range(ORDER) if point not in (left, right))
        selectors = []
        for first, second in itertools.combinations(available, 2):
            selector = result.variable(
                "minority63-q16-private-four", left, right, first, second
            )
            selectors.append(selector)
            for endpoint, point in itertools.product((left, right), (first, second)):
                result.add(-selector, -variable(endpoint, point))
                metadata["critical_nonedge_clauses"] += 1
            result.add(-selector, -variable(first, second))
            metadata["critical_nonedge_clauses"] += 1
        result.add(-edge, *selectors)
        metadata["critical_edges"] += 1
        metadata["critical_selectors"] += len(selectors)
        metadata["critical_existence_clauses"] += 1

    for deleted in range(ORDER):
        coloring = {
            (point, color): result.variable(
                "minority63-q16-deletion-color", deleted, point, color
            )
            for point in range(ORDER)
            if point != deleted
            for color in range(AUXILIARY_COLORS)
        }
        metadata["deleted_vertex_colorings"] += 1
        metadata["color_variables"] += len(coloring)
        for point in range(ORDER):
            if point == deleted:
                continue
            choices = [coloring[point, color] for color in range(AUXILIARY_COLORS)]
            result.add(*choices)
            metadata["one_hot_at_least_clauses"] += 1
            for first, second in itertools.combinations(choices, 2):
                result.add(-first, -second)
                metadata["one_hot_at_most_clauses"] += 1
        for left, right in PHYSICAL_EDGES:
            if deleted in (left, right):
                continue
            for color in range(AUXILIARY_COLORS):
                result.add(
                    -variable(left, right),
                    -coloring[left, color],
                    -coloring[right, color],
                )
                metadata["proper_edge_clauses"] += 1
    return result, metadata


def render(path: Path) -> tuple[int, int, dict[str, int]]:
    formula, metadata = build_formula()
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact-63 Q16 graph-only critical core, version 1\n")
        stream.write(
            "c order=16 edges=43 minimum_degree=5 alpha_at_most=3 "
            "omega_at_most=5 edge_critical=1 vertex_critical=1\n"
        )
        stream.write(f"p cnf {formula.variables} {len(formula.clauses)}\n")
        for clause in formula.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    return formula.variables, len(formula.clauses), metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, metadata = render(args.output)
    print(
        "MINORITY63-Q16-GRAPH-CNF-PASS "
        f"variables={variables} clauses={clauses} "
        f"critical_selectors={metadata['critical_selectors']} "
        f"deleted_colorings={metadata['deleted_vertex_colorings']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

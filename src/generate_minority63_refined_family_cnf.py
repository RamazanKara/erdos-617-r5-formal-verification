#!/usr/bin/env python3
"""Generate the three refined exact-63 unrestricted component families."""

from __future__ import annotations

import argparse
import itertools
import math
from pathlib import Path

from generate_full_k26_cnf import COLORS, ORDER, variable
from generate_full_k26_fixed_minority_graph_cnf import canonical_remaining_color_clauses
from generate_full_k26_min_degree_branch_cnf import add_at_least_k
from generate_full_k26_minority59_cnf import BASE_CLAUSES, base_clauses
from generate_full_k26_minority60_critical_cnf import add_conditional_exactly_k
from generate_local_204_cnf import CNF

BASE_VARIABLES = math.comb(ORDER, 2) * COLORS
CASES = {
    "k4_k5_r17": {
        "fixed_cliques": (tuple(range(0, 4)), tuple(range(4, 9))),
        "variable_components": ((tuple(range(9, 26)), 47),),
    },
    "k5_c10_c11": {
        "fixed_cliques": (tuple(range(0, 5)),),
        "variable_components": (
            (tuple(range(5, 15)), 24),
            (tuple(range(15, 26)), 29),
        ),
    },
    "k5_k5_r16": {
        "fixed_cliques": (tuple(range(0, 5)), tuple(range(5, 10))),
        "variable_components": ((tuple(range(10, 26)), 43),),
    },
}
MINIMUM_VARIABLE_DEGREE = 4
ADDITIONAL_PRIVATE_POINTS = 2


def build_formula(case: str) -> tuple[CNF, dict[str, int]]:
    if case not in CASES:
        raise ValueError("unknown refined exact-63 family")
    specification = CASES[case]
    fixed_cliques = specification["fixed_cliques"]
    variable_components = specification["variable_components"]
    components = tuple(fixed_cliques) + tuple(
        vertices for vertices, _edge_count in variable_components
    )
    if sorted(point for component in components for point in component) != list(
        range(ORDER)
    ):
        raise AssertionError("refined components do not partition K26")
    owner = {
        point: index for index, component in enumerate(components) for point in component
    }
    result = CNF(variables=BASE_VARIABLES)
    metadata = {
        "positive_fixed_units": 0,
        "negative_cut_units": 0,
        "variable_physical_edges": 0,
        "variable_color_zero_edges": 0,
        "minimum_degree_constraints": 0,
        "critical_edges": 0,
        "critical_selectors": 0,
        "endpoint_nonedge_clauses": 0,
        "selected_pair_nonedge_clauses": 0,
    }

    fixed_edge_set = set()
    for clique in fixed_cliques:
        fixed_edge_set.update(itertools.combinations(clique, 2))
    for left, right in itertools.combinations(range(ORDER), 2):
        literal = variable(left, right, 0)
        if (left, right) in fixed_edge_set:
            result.add(literal)
            metadata["positive_fixed_units"] += 1
        elif owner[left] != owner[right]:
            result.add(-literal)
            metadata["negative_cut_units"] += 1

    for component_index, (vertices, edge_count) in enumerate(variable_components):
        physical = tuple(itertools.combinations(vertices, 2))
        literals = [variable(left, right, 0) for left, right in physical]
        result.exactly_k(
            literals,
            edge_count,
            ("minority63-refined-family", case, component_index, "edges"),
        )
        metadata["variable_physical_edges"] += len(physical)
        metadata["variable_color_zero_edges"] += edge_count

        for point in vertices:
            add_at_least_k(
                result,
                [
                    variable(min(point, other), max(point, other), 0)
                    for other in vertices
                    if other != point
                ],
                MINIMUM_VARIABLE_DEGREE,
                ("minority63-refined-minimum-degree", case, component_index, point),
            )
            metadata["minimum_degree_constraints"] += 1

        for left, right in physical:
            gate = variable(left, right, 0)
            available = tuple(point for point in vertices if point not in (left, right))
            selected = {
                point: result.variable(
                    "minority63-refined-private-four",
                    case,
                    component_index,
                    left,
                    right,
                    point,
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
                (
                    "minority63-refined-private-four",
                    case,
                    component_index,
                    left,
                    right,
                ),
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

    for clause in canonical_remaining_color_clauses():
        result.add(*clause)

    fixed_edges = metadata["positive_fixed_units"]
    variable_edges = metadata["variable_color_zero_edges"]
    if fixed_edges + variable_edges != 63:
        raise AssertionError("refined family does not have exactly 63 color-zero edges")
    return result, metadata


def render(case: str, path: Path) -> tuple[int, int, dict[str, int]]:
    extension, metadata = build_formula(case)
    clause_count = BASE_CLAUSES + len(extension.clauses)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact-63 refined component family, version 1\n")
        stream.write(
            f"c family={case} minimum_variable_degree=4 "
            "private_independent_four_per_variable_edge=1 "
            "canonical_remaining_colors=1\n"
        )
        stream.write(f"p cnf {extension.variables} {clause_count}\n")
        observed = 0
        for clause in base_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for clause in extension.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    return extension.variables, clause_count, metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--family", choices=tuple(CASES), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, metadata = render(args.family, args.output)
    print(
        "MINORITY63-REFINED-FAMILY-CNF-PASS "
        f"family={args.family} variables={variables} clauses={clauses} "
        f"critical_edges={metadata['critical_edges']} "
        f"critical_selectors={metadata['critical_selectors']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Generate the exact K4+K5+K5+R12 subfamily at color count 63."""

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
FIXED_CLIQUES = (tuple(range(0, 4)), tuple(range(4, 9)), tuple(range(9, 14)))
RESIDUAL = tuple(range(14, 26))
RESIDUAL_EDGES = 37
MINIMUM_RESIDUAL_DEGREE = 4


def build_formula() -> tuple[CNF, dict[str, int]]:
    components = FIXED_CLIQUES + (RESIDUAL,)
    owner = {
        point: index for index, component in enumerate(components) for point in component
    }
    fixed_edges = {
        edge for clique in FIXED_CLIQUES for edge in itertools.combinations(clique, 2)
    }
    result = CNF(variables=BASE_VARIABLES)
    metadata = {
        "positive_fixed_units": 0,
        "negative_cut_units": 0,
        "critical_edges": 0,
        "critical_selectors": 0,
    }
    for left, right in itertools.combinations(range(ORDER), 2):
        literal = variable(left, right, 0)
        if (left, right) in fixed_edges:
            result.add(literal)
            metadata["positive_fixed_units"] += 1
        elif owner[left] != owner[right]:
            result.add(-literal)
            metadata["negative_cut_units"] += 1

    physical = tuple(itertools.combinations(RESIDUAL, 2))
    result.exactly_k(
        [variable(left, right, 0) for left, right in physical],
        RESIDUAL_EDGES,
        ("minority63-k4-k5-k5", "residual-edges"),
    )
    for point in RESIDUAL:
        add_at_least_k(
            result,
            [
                variable(min(point, other), max(point, other), 0)
                for other in RESIDUAL
                if other != point
            ],
            MINIMUM_RESIDUAL_DEGREE,
            ("minority63-k4-k5-k5", "minimum-degree", point),
        )
    for left, right in physical:
        gate = variable(left, right, 0)
        available = tuple(point for point in RESIDUAL if point not in (left, right))
        selected = {
            point: result.variable(
                "minority63-k4-k5-k5-private-three", left, right, point
            )
            for point in available
        }
        metadata["critical_edges"] += 1
        metadata["critical_selectors"] += len(selected)
        add_conditional_exactly_k(
            result,
            gate,
            [selected[point] for point in available],
            1,
            ("minority63-k4-k5-k5-private-three", left, right),
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
    for clause in canonical_remaining_color_clauses():
        result.add(*clause)
    if metadata["positive_fixed_units"] + RESIDUAL_EDGES != 63:
        raise AssertionError("K4+K5+K5 family edge count changed")
    return result, metadata


def render(path: Path) -> tuple[int, int, dict[str, int]]:
    extension, metadata = build_formula()
    clauses = BASE_CLAUSES + len(extension.clauses)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact-63 K4+K5+K5 component family, version 1\n")
        stream.write(
            "c residual_order=12 residual_edges=37 minimum_degree=4 "
            "private_independent_three_per_residual_edge=1\n"
        )
        stream.write(f"p cnf {extension.variables} {clauses}\n")
        observed = 0
        for clause in base_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for clause in extension.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
    if observed != clauses:
        raise AssertionError("K4+K5+K5 streamed clause count changed")
    return extension.variables, clauses, metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, metadata = render(args.output)
    print(
        "MINORITY63-K4-K5-K5-FAMILY-CNF-PASS "
        f"variables={variables} clauses={clauses} "
        f"critical_edges={metadata['critical_edges']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

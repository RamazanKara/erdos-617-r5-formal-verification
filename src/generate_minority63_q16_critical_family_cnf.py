#!/usr/bin/env python3
"""Add the proved vertex-critical witnesses to the final exact-63 Q16 family."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_full_k26_cnf import variable
from generate_full_k26_minority59_cnf import BASE_CLAUSES, base_clauses
from generate_local_204_cnf import CNF
from generate_minority63_min_degree_family_cnf import build_extensions

CASE = "k5_k5_r16"
DEGREE = 5
RESIDUAL = tuple(range(10, 26))
AUXILIARY_COLORS = 5


def build_vertex_critical_extension(starting_variables: int) -> tuple[CNF, dict[str, int]]:
    result = CNF(variables=starting_variables)
    metadata = {
        "deleted_vertex_colorings": 0,
        "color_variables": 0,
        "one_hot_at_least_clauses": 0,
        "one_hot_at_most_clauses": 0,
        "proper_edge_clauses": 0,
    }
    for deleted in RESIDUAL:
        coloring = {
            (point, color): result.variable(
                "minority63-q16-deletion-color", deleted, point, color
            )
            for point in RESIDUAL
            if point != deleted
            for color in range(AUXILIARY_COLORS)
        }
        metadata["deleted_vertex_colorings"] += 1
        metadata["color_variables"] += len(coloring)
        for point in RESIDUAL:
            if point == deleted:
                continue
            choices = [coloring[point, color] for color in range(AUXILIARY_COLORS)]
            result.add(*choices)
            metadata["one_hot_at_least_clauses"] += 1
            for first, second in itertools.combinations(choices, 2):
                result.add(-first, -second)
                metadata["one_hot_at_most_clauses"] += 1
        for left, right in itertools.combinations(RESIDUAL, 2):
            if deleted in (left, right):
                continue
            edge = variable(left, right, 0)
            for color in range(AUXILIARY_COLORS):
                result.add(-edge, -coloring[left, color], -coloring[right, color])
                metadata["proper_edge_clauses"] += 1
    return result, metadata


def build_formula() -> tuple[CNF, CNF, CNF, dict[str, int]]:
    family, branch, _branch_metadata = build_extensions(CASE, DEGREE)
    critical, metadata = build_vertex_critical_extension(branch.variables)
    return family, branch, critical, metadata


def render(path: Path) -> tuple[int, int, dict[str, int]]:
    family, branch, critical, metadata = build_formula()
    clause_count = (
        BASE_CLAUSES + len(family.clauses) + len(branch.clauses) + len(critical.clauses)
    )
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact-63 Q16 vertex-critical family, version 1\n")
        stream.write(
            "c family=k5_k5_r16 residual_minimum_degree=5 "
            "deleted_vertex_five_colorings=16 fixed_minimum_degree_vertex=1\n"
        )
        stream.write(f"p cnf {critical.variables} {clause_count}\n")
        observed = 0
        for clause in base_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for extension in (family, branch, critical):
            for clause in extension.clauses:
                stream.write(" ".join(map(str, clause)) + " 0\n")
                observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    return critical.variables, clause_count, metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, metadata = render(args.output)
    print(
        "MINORITY63-Q16-CRITICAL-FAMILY-CNF-PASS "
        f"variables={variables} clauses={clauses} "
        f"deleted_colorings={metadata['deleted_vertex_colorings']} "
        f"proper_edge_clauses={metadata['proper_edge_clauses']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

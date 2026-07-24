#!/usr/bin/env python3
"""Deterministic CNF for the equality case of the local Turan bound.

Variables x(c,d,v) say that point v lies in block B[c,d], where c != d.
Point v belongs to spoke group A_{v//5}. Variables with v in A_c do not exist.
"""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

COLORS = tuple(range(5))
POINTS = tuple(range(25))


def group(vertex: int) -> int:
    return vertex // 5


def variable_map() -> dict[tuple[int, int, int], int]:
    result: dict[tuple[int, int, int], int] = {}
    next_variable = 1
    for color in COLORS:
        for doubled_group in COLORS:
            if doubled_group == color:
                continue
            for vertex in POINTS:
                if group(vertex) == color:
                    continue
                result[color, doubled_group, vertex] = next_variable
                next_variable += 1
    assert next_variable == 401
    return result


def add_exactly_one(clauses: list[list[int]], variables: list[int]) -> None:
    clauses.append(variables)
    for left, right in itertools.combinations(variables, 2):
        clauses.append([-left, -right])


def add_exactly_two_of_five(clauses: list[list[int]], variables: list[int]) -> None:
    assert len(variables) == 5
    for triple in itertools.combinations(variables, 3):
        clauses.append([-literal for literal in triple])
    for quadruple in itertools.combinations(variables, 4):
        clauses.append(list(quadruple))


def build_cnf() -> tuple[dict[tuple[int, int, int], int], list[list[int]]]:
    variable = variable_map()
    clauses: list[list[int]] = []

    # For fixed c, the four blocks B[c,d] partition V minus A_c.
    for color in COLORS:
        block_labels = [d for d in COLORS if d != color]
        for vertex in POINTS:
            if group(vertex) != color:
                add_exactly_one(
                    clauses,
                    [variable[color, d, vertex] for d in block_labels],
                )

    # B[c,d] has two points from A_d and one from every other A_e, e != c,d.
    for color in COLORS:
        for doubled_group in COLORS:
            if doubled_group == color:
                continue
            for point_group in COLORS:
                if point_group == color:
                    continue
                variables = [
                    variable[color, doubled_group, 5 * point_group + offset]
                    for offset in range(5)
                ]
                if point_group == doubled_group:
                    add_exactly_two_of_five(clauses, variables)
                else:
                    add_exactly_one(clauses, variables)

    # Two blocks in distinct resolutions intersect in at most one point.
    for first_color, second_color in itertools.combinations(COLORS, 2):
        common_points = [
            vertex
            for vertex in POINTS
            if group(vertex) not in (first_color, second_color)
        ]
        for first_label in COLORS:
            if first_label == first_color:
                continue
            for second_label in COLORS:
                if second_label == second_color:
                    continue
                for left, right in itertools.combinations(common_points, 2):
                    clauses.append(
                        [
                            -variable[first_color, first_label, left],
                            -variable[first_color, first_label, right],
                            -variable[second_color, second_label, left],
                            -variable[second_color, second_label, right],
                        ]
                    )

        # Counting forces the unique empty intersection to be the reciprocal pair.
        for vertex in common_points:
            clauses.append(
                [
                    -variable[first_color, second_color, vertex],
                    -variable[second_color, first_color, vertex],
                ]
            )

    # Complete symmetry break for resolution 0. Within each A_e (e != 0),
    # arbitrary point permutations map the doubled pair to offsets 0,1 and the
    # three singleton points to offsets 2,3,4 in increasing block-label order.
    for point_group in range(1, 5):
        other_labels = [d for d in range(1, 5) if d != point_group]
        clauses.append([variable[0, point_group, 5 * point_group]])
        clauses.append([variable[0, point_group, 5 * point_group + 1]])
        for offset, block_label in enumerate(other_labels, start=2):
            clauses.append([variable[0, block_label, 5 * point_group + offset]])

    assert len(variable) == 400
    assert len(clauses) == 18630
    return variable, clauses


def render_dimacs() -> str:
    variable, clauses = build_cnf()
    lines = [
        "c ERDOS617 local equality compatibility, version 1",
        "c x(c,d,v): point v is in block B[c,d]; mapping is lexicographic in c,d,v",
        "c complete symmetry break fixes resolution 0 by within-group permutations",
        f"p cnf {len(variable)} {len(clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in clauses)
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(render_dimacs(), encoding="ascii", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

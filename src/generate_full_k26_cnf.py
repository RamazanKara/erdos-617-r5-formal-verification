#!/usr/bin/env python3
"""Generate the exact unrestricted balanced-coloring CNF for (26, 5, 6)."""

from __future__ import annotations

import argparse
import itertools
import math
from pathlib import Path

ORDER = 26
COLORS = 5
WITNESS_SIZE = 6


def edge_index(left: int, right: int) -> int:
    """Zero-based lexicographic index of an unordered edge of K_26."""
    if not 0 <= left < right < ORDER:
        raise ValueError("edge endpoints outside canonical range")
    return left * (2 * ORDER - left - 1) // 2 + (right - left - 1)


def variable(left: int, right: int, color: int) -> int:
    if not 0 <= color < COLORS:
        raise ValueError("color outside range")
    return COLORS * edge_index(left, right) + color + 1


def clauses():
    vertices = range(ORDER)

    # Exactly one color per unordered edge.
    for left, right in itertools.combinations(vertices, 2):
        edge_colors = [variable(left, right, color) for color in range(COLORS)]
        yield edge_colors
        for first, second in itertools.combinations(edge_colors, 2):
            yield [-first, -second]

    # Every six-set contains every color.
    for subset in itertools.combinations(vertices, WITNESS_SIZE):
        edges = tuple(itertools.combinations(subset, 2))
        for color in range(COLORS):
            yield [variable(left, right, color) for left, right in edges]

    # Safe orbit representative: name color(0,1) as 0, then use a permutation
    # of vertices 1..25 to sort all spoke colors at vertex 0.
    yield [variable(0, 1, 0)]
    for first_vertex in range(1, ORDER - 1):
        second_vertex = first_vertex + 1
        for first_color in range(COLORS):
            for second_color in range(first_color):
                yield [
                    -variable(0, first_vertex, first_color),
                    -variable(0, second_vertex, second_color),
                ]


def expected_counts() -> tuple[int, int]:
    edges = ORDER * (ORDER - 1) // 2
    variables = edges * COLORS
    exact_one = edges * (1 + COLORS * (COLORS - 1) // 2)
    witnesses = COLORS * math.comb(ORDER, WITNESS_SIZE)
    symmetry = 1 + (ORDER - 2) * COLORS * (COLORS - 1) // 2
    return variables, exact_one + witnesses + symmetry


def render(path: Path) -> None:
    variables, clause_count = expected_counts()
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact unrestricted K26 five-coloring, version 1\n")
        stream.write("c safe symmetry: sorted colors on edges (0,i), color(0,1)=0\n")
        stream.write(f"p cnf {variables} {clause_count}\n")
        observed = 0
        for clause in clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    render(args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

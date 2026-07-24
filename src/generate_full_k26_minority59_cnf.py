#!/usr/bin/env python3
"""Generate the two exact full-K26 branches with a 59-edge minority color.

Kang--Pikhurko equality at (n,r)=(26,5), together with the absence of a
monochromatic K6, leaves the all-five part vector.  Complementing their
construction gives five disjoint K5s plus a special vertex.  Subset sizes a
and 5-a are isomorphic, so a=1,2 are the two representatives.
"""

from __future__ import annotations

import argparse
import itertools
import math
from pathlib import Path

from generate_full_k26_cnf import COLORS, ORDER, WITNESS_SIZE, variable

CASES = {"a1": 1, "a2": 2}
PART_SIZE = 5
SPECIAL = 25
SOURCE = tuple(range(0, 5))
TARGET = tuple(range(5, 10))
DISTINGUISHED = 5
BASE_CLAUSES = (
    math.comb(ORDER, 2) * (1 + math.comb(COLORS, 2))
    + COLORS * math.comb(ORDER, WITNESS_SIZE)
)


def minority_edges(subset_size: int) -> set[tuple[int, int]]:
    if subset_size not in range(1, PART_SIZE):
        raise ValueError("subset size must be proper and nonempty")
    blocks = [tuple(range(5 * index, 5 * index + 5)) for index in range(5)]
    subset = set(SOURCE[:subset_size])
    edges: set[tuple[int, int]] = set()
    for block in blocks:
        edges.update(itertools.combinations(block, 2))
    for point in SOURCE:
        if point not in subset:
            edges.add(tuple(sorted((SPECIAL, point))))
    for point in TARGET:
        if point != DISTINGUISHED:
            edges.add(tuple(sorted((SPECIAL, point))))
    for point in subset:
        edges.add(tuple(sorted((DISTINGUISHED, point))))
    if len(edges) != 59:
        raise AssertionError("global extremal minority graph does not have 59 edges")
    return edges


def base_clauses():
    for left, right in itertools.combinations(range(ORDER), 2):
        colors = [variable(left, right, color) for color in range(COLORS)]
        yield colors
        for first, second in itertools.combinations(colors, 2):
            yield [-first, -second]
    for subset in itertools.combinations(range(ORDER), WITNESS_SIZE):
        pairs = tuple(itertools.combinations(subset, 2))
        for color in range(COLORS):
            yield [variable(left, right, color) for left, right in pairs]


def expected_counts() -> tuple[int, int]:
    return math.comb(ORDER, 2) * COLORS, BASE_CLAUSES + math.comb(ORDER, 2) + 1


def render(case: str, path: Path) -> tuple[int, int]:
    if case not in CASES:
        raise ValueError("unknown 59-edge minority case")
    fixed = minority_edges(CASES[case])
    variables, clause_count = expected_counts()
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact unrestricted K26 minority-59 branch, version 1\n")
        stream.write(f"c case={case} subset_size={CASES[case]} fixed_color_zero=1\n")
        stream.write(f"p cnf {variables} {clause_count}\n")
        observed = 0
        for clause in base_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for left, right in itertools.combinations(range(ORDER), 2):
            literal = variable(left, right, 0)
            stream.write(f"{literal if (left, right) in fixed else -literal} 0\n")
            observed += 1
        # Edge (0,6) is outside the fixed color-zero graph.  The remaining
        # four colors are interchangeable, so name its color as one.
        if (0, 6) in fixed:
            raise AssertionError("remaining-color symmetry edge became color zero")
        stream.write(f"{variable(0, 6, 1)} 0\n")
        observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    return variables, clause_count


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", choices=tuple(CASES), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.case, args.output)
    print(
        "FULL-K26-MINORITY59-CNF-PASS "
        f"case={args.case} variables={variables} clauses={clauses}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Generate exact-60 fixed-witness branches with canonical remaining colors."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_full_k26_cnf import COLORS, ORDER, variable
from generate_full_k26_minority59_cnf import BASE_CLAUSES, base_clauses
from generate_full_k26_minority60_cnf import MINIMUM_DEGREES
from generate_full_k26_minority60_fixed_witness_cnf import build_extensions
from generate_local_204_cnf import CNF


def canonical_extension(critical: CNF) -> CNF:
    cnf = CNF(variables=critical.variables)

    # The selected private witness for edge (0,1) is represented canonically,
    # rather than merely existing alongside the already fixed six-set units.
    for point in range(ORDER):
        if point in (0, 1):
            continue
        selector = critical.names["private-six-set", 0, 1, point]
        cnf.add(selector if point in (2, 3, 4, 5) else -selector)

    # Name colors 1,...,4 by their first occurrence in lexicographic edge
    # order.  Edge (0,2), already fixed to color 1, is the first nonzero edge.
    edges = tuple(itertools.combinations(range(ORDER), 2))
    for index, (left, right) in enumerate(edges):
        earlier = edges[:index]
        for color in range(2, COLORS):
            cnf.add(
                -variable(left, right, color),
                *[
                    variable(first, second, color - 1)
                    for first, second in earlier
                ],
            )
    return cnf


def expected_counts(degree: int) -> tuple[int, int, int]:
    global_count, degrees, orbit, critical, _ = build_extensions(degree)
    canonical = canonical_extension(critical)
    parts = (global_count, degrees, orbit, critical, canonical)
    return (
        canonical.variables,
        BASE_CLAUSES + sum(len(part.clauses) for part in parts),
        len(canonical.clauses),
    )


def render(degree: int, path: Path) -> tuple[int, int]:
    global_count, degrees, orbit, critical, _ = build_extensions(degree)
    canonical = canonical_extension(critical)
    parts = (global_count, degrees, orbit, critical, canonical)
    variables = canonical.variables
    clause_count = BASE_CLAUSES + sum(len(part.clauses) for part in parts)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(
            "c ERDOS617 exact unrestricted K26 minority-60 canonical-witness "
            "branch, version 1\n"
        )
        stream.write(
            f"c color_zero_edges=60 minimum_degree={degree} "
            "fixed_private_selector=1 first_occurrence_colors=1\n"
        )
        stream.write(f"p cnf {variables} {clause_count}\n")
        observed = 0
        for clause in base_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for part in parts:
            for clause in part.clauses:
                stream.write(" ".join(map(str, clause)) + " 0\n")
                observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    if len(canonical.clauses) != 999:
        raise AssertionError("canonical-witness clause count changed")
    return variables, clause_count


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--minimum-degree", type=int, choices=MINIMUM_DEGREES, required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.minimum_degree, args.output)
    print(
        "FULL-K26-MINORITY60-CANONICAL-WITNESS-CNF-PASS "
        f"minimum_degree={args.minimum_degree} variables={variables} clauses={clauses}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

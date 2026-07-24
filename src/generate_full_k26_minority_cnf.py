#!/usr/bin/env python3
"""Generate an exact unrestricted K26 formula with a minority-color orbit fix.

Every five-coloring has a color used on at most 65 edges.  In a balanced
coloring, that color has no isolated vertex: otherwise its restriction to the
other 25 vertices has independence number at most four and hence at least 66
edges by Turan's theorem.  A minimum-degree vertex in the minority color
therefore has degree between one and five.  Relabel that color and vertex as
zero, name one color-zero neighbor as vertex one, and sort all spoke colors.
The resulting symmetry conditions retain a representative of every orbit.
"""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_full_k26_cnf import (
    COLORS,
    ORDER,
    clauses as unrestricted_clauses,
    expected_counts as unrestricted_counts,
    variable,
)
from generate_local_204_cnf import CNF

MINORITY_EDGE_BOUND = 65
BASE_VARIABLES, BASE_CLAUSES = unrestricted_counts()


def add_at_most_k(
    cnf: CNF, literals: list[int], bound: int, label: tuple[object, ...]
) -> None:
    """Full unary dynamic-programming encoding of sum(literals) <= bound."""

    if not 0 <= bound <= len(literals):
        raise ValueError("cardinality bound outside range")
    if bound == len(literals):
        return

    limit = bound + 1
    counter: dict[tuple[int, int], int] = {}
    for index, literal in enumerate(literals, start=1):
        for count in range(1, min(index, limit) + 1):
            current = cnf.variable("counter", *label, index, count)
            counter[index, count] = current
            previous_same = counter.get((index - 1, count))
            if count == 1:
                if previous_same is not None:
                    cnf.add(-previous_same, current)
                    cnf.add(-current, previous_same, literal)
                else:
                    cnf.add(-current, literal)
                cnf.add(-literal, current)
            else:
                previous_lower = counter[index - 1, count - 1]
                if previous_same is not None:
                    cnf.add(-previous_same, current)
                    cnf.add(-current, previous_same, previous_lower)
                    cnf.add(-current, previous_same, literal)
                else:
                    cnf.add(-current, previous_lower)
                    cnf.add(-current, literal)
                cnf.add(-previous_lower, -literal, current)

    cnf.add(-counter[len(literals), bound + 1])


def minority_extension() -> CNF:
    cnf = CNF(variables=BASE_VARIABLES)
    color_zero_edges = [
        variable(left, right, 0)
        for left, right in itertools.combinations(range(ORDER), 2)
    ]
    add_at_most_k(
        cnf,
        color_zero_edges,
        MINORITY_EDGE_BOUND,
        ("minority-color-zero",),
    )
    return cnf


def expected_counts() -> tuple[int, int, int]:
    extension = minority_extension()
    # Existing sorted-spoke symmetry plus this unit means d_0(0) <= 5.
    return extension.variables, BASE_CLAUSES + 1 + len(extension.clauses), len(
        extension.clauses
    )


def render(path: Path) -> tuple[int, int]:
    extension = minority_extension()
    variables = extension.variables
    clause_count = BASE_CLAUSES + 1 + len(extension.clauses)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact unrestricted K26 minority orbit, version 1\n")
        stream.write(
            "c color 0 has at most 65 edges; sorted spokes; 1 <= d_0(0) <= 5\n"
        )
        stream.write(f"p cnf {variables} {clause_count}\n")
        observed = 0
        for clause in unrestricted_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        stream.write(f"{-variable(0, 6, 0)} 0\n")
        observed += 1
        for clause in extension.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    return variables, clause_count


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.output)
    print(
        "FULL-K26-MINORITY-CNF-PASS "
        f"variables={variables} clauses={clauses} edge_bound={MINORITY_EDGE_BOUND}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

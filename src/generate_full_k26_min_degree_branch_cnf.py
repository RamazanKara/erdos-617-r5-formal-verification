#!/usr/bin/env python3
"""Generate exhaustive minimum-degree branches of the E016 exact formula."""

from __future__ import annotations

import argparse
from pathlib import Path

from generate_full_k26_cnf import (
    COLORS,
    ORDER,
    clauses as unrestricted_clauses,
    variable,
)
from generate_full_k26_minority_cnf import (
    BASE_CLAUSES,
    minority_extension,
)
from generate_local_204_cnf import CNF

MINIMUM_DEGREES = tuple(range(1, 6))


def add_at_least_k(
    cnf: CNF, literals: list[int], bound: int, label: tuple[object, ...]
) -> None:
    """Full unary dynamic-programming encoding of sum(literals) >= bound."""

    if not 0 <= bound <= len(literals):
        raise ValueError("cardinality bound outside range")
    if bound == 0:
        return
    if bound == 1:
        cnf.add(*literals)
        return

    counter: dict[tuple[int, int], int] = {}
    for index, literal in enumerate(literals, start=1):
        for count in range(1, min(index, bound) + 1):
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

    cnf.add(counter[len(literals), bound])


def branch_extension(degree: int, starting_variables: int) -> CNF:
    if degree not in MINIMUM_DEGREES:
        raise ValueError("minority minimum degree must lie in [1,5]")
    cnf = CNF(variables=starting_variables)

    # The E016 prefix already fixes spoke 1 to color zero, sorts all spokes,
    # and forbids spoke 6 from having color zero.
    if degree > 1:
        cnf.add(variable(0, degree, 0))
    if degree < 5:
        cnf.add(-variable(0, degree + 1, 0))

    for vertex in range(1, ORDER):
        incident = [
            variable(min(vertex, other), max(vertex, other), 0)
            for other in range(ORDER)
            if other != vertex
        ]
        add_at_least_k(
            cnf,
            incident,
            degree,
            ("minority-minimum-degree", degree, vertex),
        )
    return cnf


def build_extensions(degree: int) -> tuple[CNF, CNF]:
    minority = minority_extension()
    branch = branch_extension(degree, minority.variables)
    return minority, branch


def expected_counts(degree: int) -> tuple[int, int, int]:
    minority, branch = build_extensions(degree)
    clauses = BASE_CLAUSES + 1 + len(minority.clauses) + len(branch.clauses)
    return branch.variables, clauses, len(branch.clauses)


def render(degree: int, path: Path) -> tuple[int, int]:
    minority, branch = build_extensions(degree)
    variables = branch.variables
    clause_count = (
        BASE_CLAUSES + 1 + len(minority.clauses) + len(branch.clauses)
    )
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(
            "c ERDOS617 exact unrestricted K26 minority min-degree branch, "
            "version 1\n"
        )
        stream.write(
            f"c color 0 has at most 65 edges; sorted spokes; min_degree={degree}\n"
        )
        stream.write(f"p cnf {variables} {clause_count}\n")
        observed = 0
        for clause in unrestricted_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        stream.write(f"{-variable(0, 6, 0)} 0\n")
        observed += 1
        for clause in minority.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for clause in branch.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    return variables, clause_count


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--minimum-degree", type=int, choices=MINIMUM_DEGREES, required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.minimum_degree, args.output)
    print(
        "FULL-K26-MIN-DEGREE-CNF-PASS "
        f"minimum_degree={args.minimum_degree} variables={variables} clauses={clauses}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

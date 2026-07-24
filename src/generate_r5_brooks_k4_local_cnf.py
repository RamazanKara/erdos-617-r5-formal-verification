#!/usr/bin/env python3
"""Generate E040 branch 19 with all K4-containing admissibility clauses."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_r5_brooks_exterior_sorted_cnf import build_sorted_branch
from generate_r5_five_regular_brooks_cnf import ORDER, edge_variable

BRANCH = 19
K4 = (1, 2, 3, 4)
OUTSIDE = tuple(vertex for vertex in range(ORDER) if vertex not in K4)


def local_admissibility_clauses(cnf) -> list[list[int]]:
    fixed = set(itertools.combinations(K4, 2))
    clauses: list[list[int]] = []
    for x, y in itertools.combinations(OUTSIDE, 2):
        vertices = (*K4, x, y)
        remaining = [
            edge_variable(cnf, left, right)
            for left, right in itertools.combinations(vertices, 2)
            if tuple(sorted((left, right))) not in fixed
        ]
        if len(remaining) != 9 or len(set(remaining)) != 9:
            raise AssertionError("K4-plus-pair remainder does not have nine edges")
        for forbidden in itertools.combinations(remaining, 6):
            clauses.append([-variable for variable in forbidden])
    return clauses


def build_instance():
    cnf = build_sorted_branch(BRANCH)
    for clause in local_admissibility_clauses(cnf):
        cnf.add(*clause)
    return cnf


def render(path: Path) -> tuple[int, int]:
    cnf = build_instance()
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 E040 K4-local admissibility, version 1\n")
        stream.write("c neighborhood_branch=19 core=1,2,3,4 local_edge_bound=11\n")
        stream.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    return cnf.variables, len(cnf.clauses)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.output)
    print(
        "R5-BROOKS-K4-LOCAL-CNF-PASS "
        f"branch={BRANCH} variables={variables} clauses={clauses} "
        "pairs=231 local_clauses=19404"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

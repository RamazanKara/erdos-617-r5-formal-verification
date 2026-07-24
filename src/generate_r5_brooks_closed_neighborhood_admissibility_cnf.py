#!/usr/bin/env python3
"""Generate E044 branches with every four-core admissibility consequence."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_r5_brooks_exterior_sorted_cnf import build_sorted_branch
from generate_r5_brooks_neighborhood_branch_cnf import NEIGHBOR_EDGES, representatives
from generate_r5_five_regular_brooks_cnf import ORDER, edge_variable

BRANCHES = tuple(range(20, 26))
CLOSED_NEIGHBORHOOD = tuple(range(6))
EXPECTED_NEW_CLAUSES = {
    20: 38577,
    21: 59598,
    22: 91476,
    23: 88704,
    24: 53130,
    25: 82236,
}


def fixed_closed_edge(branch: int, left: int, right: int) -> bool:
    if left == right or left not in CLOSED_NEIGHBORHOOD or right not in CLOSED_NEIGHBORHOOD:
        raise ValueError("fixed closed-neighborhood edge has invalid endpoints")
    if left == 0 or right == 0:
        return True
    pair = tuple(sorted((left - 1, right - 1)))
    index = NEIGHBOR_EDGES.index(pair)
    return bool(representatives()[branch] & (1 << index))


def four_core_admissibility_clauses(cnf, branch: int) -> list[list[int]]:
    if branch not in BRANCHES:
        raise ValueError("E044 branch outside range")
    clauses: list[list[int]] = []
    for core in itertools.combinations(CLOSED_NEIGHBORHOOD, 4):
        fixed_pairs = set(itertools.combinations(core, 2))
        fixed_count = sum(fixed_closed_edge(branch, left, right) for left, right in fixed_pairs)
        threshold = 12 - fixed_count
        if threshold > 9:
            continue
        outside = tuple(vertex for vertex in range(ORDER) if vertex not in core)
        for x, y in itertools.combinations(outside, 2):
            # Canonicalize the six-set order.  Clause literal order is
            # semantically irrelevant, but keeping it increasing makes the
            # emitted certificate instance byte-stable and independently
            # reproducible without relying on the order in which the two
            # exterior vertices were appended.
            vertices = tuple(sorted((*core, x, y)))
            remaining = [
                edge_variable(cnf, left, right)
                for left, right in itertools.combinations(vertices, 2)
                if tuple(sorted((left, right))) not in fixed_pairs
            ]
            if len(remaining) != 9 or len(set(remaining)) != 9:
                raise AssertionError("closed-neighborhood four-core remainder differs")
            for forbidden in itertools.combinations(remaining, threshold):
                clauses.append([-variable for variable in forbidden])
    if len(clauses) != EXPECTED_NEW_CLAUSES[branch]:
        raise AssertionError(f"branch {branch}: E044 clause count changed")
    return clauses


def build_instance(branch: int):
    cnf = build_sorted_branch(branch)
    for clause in four_core_admissibility_clauses(cnf, branch):
        cnf.add(*clause)
    return cnf


def render(branch: int, path: Path) -> tuple[int, int, int]:
    cnf = build_instance(branch)
    added = EXPECTED_NEW_CLAUSES[branch]
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 E044 closed-neighborhood four-core admissibility, version 1\n")
        stream.write(
            f"c neighborhood_branch={branch:02d} mask={representatives()[branch]} "
            f"four_core_clauses={added}\n"
        )
        stream.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    return cnf.variables, len(cnf.clauses), added


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=BRANCHES, required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, added = render(args.branch, args.output)
    print(
        "R5-BROOKS-CLOSED-NEIGHBORHOOD-ADMISSIBILITY-CNF-PASS "
        f"branch={args.branch:02d} variables={variables} clauses={clauses} "
        f"four_core_clauses={added}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

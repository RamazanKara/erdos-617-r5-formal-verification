#!/usr/bin/env python3
"""Generate E045 zero-cross-pattern anchor quotients for branches 20--25."""

from __future__ import annotations

import argparse
import itertools
from pathlib import Path

from generate_r5_brooks_closed_neighborhood_admissibility_cnf import (
    BRANCHES,
    EXPECTED_NEW_CLAUSES,
    four_core_admissibility_clauses,
)
from generate_r5_brooks_neighborhood_branch_cnf import (
    NEIGHBORS,
    build_branch,
    representatives,
)
from generate_r5_five_regular_brooks_cnf import edge_variable

ANCHOR = 6
ANCHOR_NEIGHBORS = tuple(range(7, 12))
ANCHOR_NONNEIGHBORS = tuple(range(12, 26))
SORT_CLASSES = (ANCHOR_NEIGHBORS, ANCHOR_NONNEIGHBORS)
ANCHOR_UNITS = 5 + 19
ANCHOR_NEIGHBORHOOD_CLAUSES = 120
EXPECTED_CROSS_STUBS = {20: 12, 21: 10, 22: 8, 23: 8, 24: 10, 25: 8}


def cross_stub_count(branch: int) -> int:
    mask = representatives()[branch]
    degrees = [0] * len(NEIGHBORS)
    neighbor_edges = tuple(itertools.combinations(range(len(NEIGHBORS)), 2))
    for index, (left, right) in enumerate(neighbor_edges):
        if mask & (1 << index):
            degrees[left] += 1
            degrees[right] += 1
    stubs = sum(4 - degree for degree in degrees)
    if stubs != EXPECTED_CROSS_STUBS[branch] or stubs >= 20:
        raise AssertionError(f"branch {branch}: zero-anchor stub premise changed")
    return stubs


def anchor_units(cnf, branch: int) -> list[int]:
    if branch not in BRANCHES:
        raise ValueError("E045 branch outside range")
    cross_stub_count(branch)
    units = [-edge_variable(cnf, ANCHOR, neighbor) for neighbor in NEIGHBORS]
    units.extend(
        edge_variable(cnf, ANCHOR, exterior)
        if exterior in ANCHOR_NEIGHBORS
        else -edge_variable(cnf, ANCHOR, exterior)
        for exterior in (*ANCHOR_NEIGHBORS, *ANCHOR_NONNEIGHBORS)
    )
    if len(units) != ANCHOR_UNITS or sum(literal > 0 for literal in units) != 5:
        raise AssertionError("zero anchor does not have its exact exterior neighborhood")
    return units


def add_within_class_sorts(cnf) -> None:
    for vertices in SORT_CLASSES:
        for left, right in zip(vertices[:-1], vertices[1:], strict=True):
            first = [edge_variable(cnf, neighbor, left) for neighbor in NEIGHBORS]
            second = [edge_variable(cnf, neighbor, right) for neighbor in NEIGHBORS]
            cnf.lexicographic_leq(
                first,
                second,
                ("zero-anchor-pattern", left, right),
            )


def anchor_neighborhood_clauses(cnf) -> list[list[int]]:
    internal = [
        edge_variable(cnf, left, right)
        for left, right in itertools.combinations(ANCHOR_NEIGHBORS, 2)
    ]
    clauses = [
        [-variable for variable in forbidden]
        for forbidden in itertools.combinations(internal, 7)
    ]
    if len(internal) != 10 or len(clauses) != ANCHOR_NEIGHBORHOOD_CLAUSES:
        raise AssertionError("anchor-neighborhood at-most-six encoding changed")
    return clauses


def build_instance(branch: int):
    if branch not in BRANCHES:
        raise ValueError("E045 branch outside range")
    cnf = build_branch(branch)
    for literal in anchor_units(cnf, branch):
        cnf.add(literal)
    add_within_class_sorts(cnf)
    for clause in four_core_admissibility_clauses(cnf, branch):
        cnf.add(*clause)
    for clause in anchor_neighborhood_clauses(cnf):
        cnf.add(*clause)
    return cnf


def render(branch: int, path: Path) -> tuple[int, int]:
    cnf = build_instance(branch)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 E045 zero-pattern anchor quotient, version 1\n")
        stream.write(
            f"c branch={branch:02d} mask={representatives()[branch]} anchor={ANCHOR} "
            f"anchor_neighbors={','.join(map(str, ANCHOR_NEIGHBORS))} "
            f"four_core_clauses={EXPECTED_NEW_CLAUSES[branch]}\n"
        )
        stream.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    return cnf.variables, len(cnf.clauses)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=BRANCHES, required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.branch, args.output)
    print(
        "R5-BROOKS-ZERO-ANCHOR-QUOTIENT-CNF-PASS "
        f"branch={args.branch:02d} cross_stubs={cross_stub_count(args.branch)} "
        f"guaranteed_zero_rows={20 - cross_stub_count(args.branch)} "
        f"variables={variables} clauses={clauses} anchor_units={ANCHOR_UNITS} "
        f"sort_comparisons=17 anchor_neighborhood_clauses=120"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

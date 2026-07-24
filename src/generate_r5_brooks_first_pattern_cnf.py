#!/usr/bin/env python3
"""Generate one E039 first-exterior-pattern child formula."""

from __future__ import annotations

import argparse
from pathlib import Path

from generate_r5_brooks_exterior_sorted_cnf import build_sorted_branch
from generate_r5_brooks_neighborhood_branch_cnf import NEIGHBORS, representatives
from generate_r5_five_regular_brooks_cnf import edge_variable

FIRST_EXTERIOR = 6
PATTERN_COUNT = 1 << len(NEIGHBORS)


def first_pattern_units(cnf, pattern: int) -> list[int]:
    if not 0 <= pattern < PATTERN_COUNT:
        raise ValueError("first exterior pattern outside five-bit range")
    units: list[int] = []
    for index, neighbor in enumerate(NEIGHBORS):
        variable = edge_variable(cnf, neighbor, FIRST_EXTERIOR)
        units.append(variable if pattern & (1 << index) else -variable)
    return units


def build_child(branch: int, pattern: int):
    cnf = build_sorted_branch(branch)
    for literal in first_pattern_units(cnf, pattern):
        cnf.add(literal)
    return cnf


def render(branch: int, pattern: int, path: Path) -> tuple[int, int, int]:
    catalog = representatives()
    if not 0 <= branch < len(catalog):
        raise ValueError("neighborhood branch outside range")
    cnf = build_child(branch, pattern)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 E039 first exterior pattern child, version 1\n")
        stream.write(
            f"c branch={branch:02d} neighborhood_mask={catalog[branch]} "
            f"first_pattern={pattern:02d}\n"
        )
        stream.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    return cnf.variables, len(cnf.clauses), catalog[branch]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=range(26), required=True)
    parser.add_argument("--pattern", type=int, choices=range(PATTERN_COUNT), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, mask = render(args.branch, args.pattern, args.output)
    print(
        "R5-BROOKS-FIRST-PATTERN-CNF-PASS "
        f"branch={args.branch:02d} mask={mask} pattern={args.pattern:02d} "
        f"variables={variables} clauses={clauses} children=32"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

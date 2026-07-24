#!/usr/bin/env python3
"""Generate an E037 branch with safely sorted exterior adjacency patterns."""

from __future__ import annotations

import argparse
from pathlib import Path

from generate_r5_brooks_neighborhood_branch_cnf import (
    NEIGHBORS,
    build_branch,
    representatives,
)
from generate_r5_five_regular_brooks_cnf import edge_variable

EXTERIOR = tuple(range(6, 26))


def build_sorted_branch(branch: int):
    cnf = build_branch(branch)
    for left, right in zip(EXTERIOR[:-1], EXTERIOR[1:], strict=True):
        first = [edge_variable(cnf, neighbor, left) for neighbor in NEIGHBORS]
        second = [edge_variable(cnf, neighbor, right) for neighbor in NEIGHBORS]
        cnf.lexicographic_leq(first, second, ("exterior-pattern", left, right))
    return cnf


def render(branch: int, path: Path) -> tuple[int, int, int]:
    catalog = representatives()
    if not 0 <= branch < len(catalog):
        raise ValueError("neighborhood branch outside range")
    mask = catalog[branch]
    cnf = build_sorted_branch(branch)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 E038 sorted-exterior Brooks branch, version 1\n")
        stream.write(
            f"c branch={branch:02d} neighborhood_mask={mask} "
            "exterior_patterns_lex_nondecreasing=1\n"
        )
        stream.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    return cnf.variables, len(cnf.clauses), mask


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=range(26), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, mask = render(args.branch, args.output)
    print(
        "R5-BROOKS-EXTERIOR-SORTED-CNF-PASS "
        f"branch={args.branch:02d} mask={mask} variables={variables} "
        f"clauses={clauses} comparisons=19 pattern_bits=5"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

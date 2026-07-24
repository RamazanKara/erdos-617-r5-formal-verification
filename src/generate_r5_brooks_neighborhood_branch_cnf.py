#!/usr/bin/env python3
"""Generate one exhaustive E037 neighborhood-isomorphism branch."""

from __future__ import annotations

import argparse
import itertools
from collections import Counter
from pathlib import Path

from generate_r5_five_regular_brooks_cnf import build_instance, edge_variable

NEIGHBORS = tuple(range(1, 6))
NEIGHBOR_EDGES = tuple(itertools.combinations(range(5), 2))
MAX_INTERNAL_EDGES = 6


def relabel_mask(mask: int, permutation: tuple[int, ...]) -> int:
    present = {
        edge for index, edge in enumerate(NEIGHBOR_EDGES) if mask & (1 << index)
    }
    result = 0
    for index, (left, right) in enumerate(NEIGHBOR_EDGES):
        preimage = tuple(sorted((permutation[left], permutation[right])))
        if preimage in present:
            result |= 1 << index
    return result


def canonical_mask(mask: int) -> int:
    if not 0 <= mask < 1 << len(NEIGHBOR_EDGES):
        raise ValueError("five-vertex graph mask outside range")
    return min(
        relabel_mask(mask, permutation)
        for permutation in itertools.permutations(range(5))
    )


def representatives() -> tuple[int, ...]:
    canonical = {canonical_mask(mask) for mask in range(1 << len(NEIGHBOR_EDGES))}
    result = tuple(
        mask for mask in sorted(canonical) if mask.bit_count() <= MAX_INTERNAL_EDGES
    )
    distribution = Counter(mask.bit_count() for mask in result)
    if len(result) != 26 or distribution != Counter({0: 1, 1: 1, 2: 2, 3: 4, 4: 6, 5: 6, 6: 6}):
        raise AssertionError("five-neighbor isomorphism catalog changed")
    return result


def branch_units(cnf, branch: int) -> list[int]:
    catalog = representatives()
    if not 0 <= branch < len(catalog):
        raise ValueError("neighborhood branch outside range")
    mask = catalog[branch]
    units: list[int] = []
    for index, (left, right) in enumerate(itertools.combinations(NEIGHBORS, 2)):
        variable = edge_variable(cnf, left, right)
        units.append(variable if mask & (1 << index) else -variable)
    return units


def build_branch(branch: int):
    cnf = build_instance()
    for literal in branch_units(cnf, branch):
        cnf.add(literal)
    return cnf


def render(branch: int, path: Path) -> tuple[int, int, int]:
    catalog = representatives()
    cnf = build_branch(branch)
    mask = catalog[branch]
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 E037 r=5 Brooks neighborhood branch, version 1\n")
        stream.write(
            f"c branch={branch:02d} neighborhood_mask={mask} "
            f"internal_edges={mask.bit_count()}\n"
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
        "R5-BROOKS-NEIGHBORHOOD-BRANCH-CNF-PASS "
        f"branch={args.branch:02d} mask={mask} internal_edges={mask.bit_count()} "
        f"variables={variables} clauses={clauses} branches=26"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

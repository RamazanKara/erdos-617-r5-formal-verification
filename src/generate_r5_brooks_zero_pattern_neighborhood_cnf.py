#!/usr/bin/env python3
"""Generate one E043 zero-pattern anchor-neighborhood child."""

from __future__ import annotations

import argparse
import itertools
from collections import Counter
from pathlib import Path

from generate_r5_brooks_branch19_cross_pattern_cnf import (
    build_child as build_e042,
    ordered_exterior_patterns,
)
from generate_r5_brooks_exterior_sorted_cnf import EXTERIOR
from generate_r5_five_regular_brooks_cnf import edge_variable

OPEN_PARENTS = (4, 9, 19)
EXPECTED_CHILD_COUNTS = {4: 26, 9: 16, 19: 5}
ANCHOR = EXTERIOR[0]


def permute_pattern(pattern: int, permutation: tuple[int, ...]) -> int:
    result = pattern & (1 << 4)
    for old_column in range(4):
        if pattern & (1 << old_column):
            result |= 1 << permutation[old_column]
    return result


def pattern_vertices(parent: int) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    if parent not in OPEN_PARENTS:
        raise ValueError("E043 parent is not one of the three open E042 children")
    patterns = ordered_exterior_patterns(parent)
    zero = tuple(vertex for vertex, pattern in zip(EXTERIOR, patterns, strict=True) if pattern == 0)
    nonzero = tuple(vertex for vertex, pattern in zip(EXTERIOR, patterns, strict=True) if pattern != 0)
    nonzero_patterns = tuple(pattern for pattern in patterns if pattern != 0)
    if not zero or zero[0] != ANCHOR:
        raise AssertionError("first exterior vertex is no longer a zero-pattern anchor")
    return zero, nonzero, nonzero_patterns


def stabilizer_actions(parent: int) -> tuple[tuple[int, ...], ...]:
    _, _, patterns = pattern_vertices(parent)
    actions: set[tuple[int, ...]] = set()
    for permutation in itertools.permutations(range(4)):
        transformed = tuple(permute_pattern(pattern, permutation) for pattern in patterns)
        if Counter(transformed) != Counter(patterns):
            continue
        choices = tuple(
            tuple(index for index, target in enumerate(patterns) if target == pattern)
            for pattern in transformed
        )
        for action in itertools.product(*choices):
            if len(set(action)) == len(patterns):
                actions.add(tuple(action))
    if not actions:
        raise AssertionError("cross-pattern stabilizer is empty")
    return tuple(sorted(actions))


def image_subset(mask: int, action: tuple[int, ...]) -> int:
    return sum(1 << action[index] for index in range(len(action)) if mask & (1 << index))


def canonical_subset(parent: int, mask: int) -> int:
    return min(image_subset(mask, action) for action in stabilizer_actions(parent))


def neighbor_subset_representatives(parent: int) -> tuple[int, ...]:
    _, nonzero, _ = pattern_vertices(parent)
    result = {
        canonical_subset(parent, mask)
        for mask in range(1 << len(nonzero))
        if mask.bit_count() <= 5
    }
    ordered = tuple(sorted(result))
    if len(ordered) != EXPECTED_CHILD_COUNTS[parent]:
        raise AssertionError(f"parent {parent}: zero-anchor orbit catalog changed")
    return ordered


def anchor_neighborhood_units(cnf, parent: int, child: int) -> list[int]:
    catalog = neighbor_subset_representatives(parent)
    if not 0 <= child < len(catalog):
        raise ValueError("E043 local child outside range")
    zero, nonzero, _ = pattern_vertices(parent)
    subset = catalog[child]
    selected_nonzero = {
        vertex for index, vertex in enumerate(nonzero) if subset & (1 << index)
    }
    zero_count = 5 - len(selected_nonzero)
    zero_remaining = zero[1:]
    if not 0 <= zero_count <= len(zero_remaining):
        raise AssertionError("degree-five anchor split has invalid zero-neighbor count")
    selected = set(zero_remaining[:zero_count]) | selected_nonzero
    units: list[int] = []
    for vertex in EXTERIOR:
        if vertex == ANCHOR:
            continue
        variable = edge_variable(cnf, ANCHOR, vertex)
        units.append(variable if vertex in selected else -variable)
    if len(units) != 19 or sum(literal > 0 for literal in units) != 5:
        raise AssertionError("anchor neighborhood does not fix exactly five exterior neighbors")
    return units


def build_child(parent: int, child: int):
    cnf = build_e042(parent)
    for literal in anchor_neighborhood_units(cnf, parent, child):
        cnf.add(literal)
    return cnf


def render(parent: int, child: int, path: Path) -> tuple[int, int, int, int]:
    catalog = neighbor_subset_representatives(parent)
    cnf = build_child(parent, child)
    subset = catalog[child]
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 E043 zero-pattern anchor-neighborhood child, version 1\n")
        stream.write(
            f"c e042_parent={parent:02d} local_child={child:02d} anchor={ANCHOR} "
            f"nonzero_subset_mask={subset} zero_neighbors={5 - subset.bit_count()}\n"
        )
        stream.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    return cnf.variables, len(cnf.clauses), subset, len(catalog)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--parent", type=int, choices=OPEN_PARENTS, required=True)
    parser.add_argument("--child", type=int, required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, subset, children = render(args.parent, args.child, args.output)
    print(
        "R5-BROOKS-ZERO-PATTERN-NEIGHBORHOOD-CNF-PASS "
        f"parent={args.parent:02d} child={args.child:02d} children={children} "
        f"subset_mask={subset} variables={variables} clauses={clauses} anchor_units=19"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

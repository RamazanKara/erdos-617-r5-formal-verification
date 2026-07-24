#!/usr/bin/env python3
"""Generate one exact E042 cross-pattern child of open Brooks branch 19."""

from __future__ import annotations

import argparse
import itertools
from collections import Counter
from pathlib import Path

from generate_r5_brooks_exterior_sorted_cnf import EXTERIOR
from generate_r5_brooks_k4_local_cnf import BRANCH, build_instance as build_e040
from generate_r5_brooks_neighborhood_branch_cnf import NEIGHBORS, representatives as neighborhood_representatives
from generate_r5_five_regular_brooks_cnf import edge_variable

K4_COLUMNS = tuple(range(4))
FIFTH_STUBS = tuple(range(4, 8))
STUBS = K4_COLUMNS + FIFTH_STUBS
EXPECTED_NONZERO_ROW_DISTRIBUTION = Counter({4: 5, 5: 7, 6: 5, 7: 2, 8: 1})
EXPECTED_REPRESENTATIVES = (
    (1, 2, 4, 8, 16, 16, 16, 16),
    (1, 2, 4, 16, 16, 16, 24),
    (1, 2, 12, 16, 16, 16, 16),
    (1, 2, 16, 16, 16, 28),
    (1, 2, 16, 16, 20, 24),
    (1, 6, 16, 16, 16, 24),
    (1, 14, 16, 16, 16, 16),
    (1, 16, 16, 16, 30),
    (1, 16, 16, 18, 28),
    (1, 16, 18, 20, 24),
    (3, 12, 16, 16, 16, 16),
    (3, 16, 16, 16, 28),
    (3, 16, 16, 20, 24),
    (7, 16, 16, 16, 24),
    (15, 16, 16, 16, 16),
    (16, 16, 16, 31),
    (16, 16, 17, 30),
    (16, 16, 19, 28),
    (16, 17, 18, 28),
    (17, 18, 20, 24),
)


def set_partitions(items: tuple[int, ...]):
    """Enumerate every set partition once, with blocks ordered by minima."""
    if not items:
        yield ()
        return
    first = items[0]
    for tail in set_partitions(items[1:]):
        yield ((first,), *tail)
        for index, block in enumerate(tail):
            yield tail[:index] + ((first, *block),) + tail[index + 1 :]


def signature(partition: tuple[tuple[int, ...], ...], permutation: tuple[int, ...]) -> tuple[int, ...]:
    patterns: list[int] = []
    for block in partition:
        pattern = 0
        for stub in block:
            if stub in K4_COLUMNS:
                pattern |= 1 << permutation[stub]
            else:
                pattern |= 1 << 4
        patterns.append(pattern)
    return tuple(sorted(patterns))


def canonical_signature(partition: tuple[tuple[int, ...], ...]) -> tuple[int, ...]:
    return min(
        signature(partition, permutation)
        for permutation in itertools.permutations(K4_COLUMNS)
    )


def representatives() -> tuple[tuple[int, ...], ...]:
    result = {
        canonical_signature(partition)
        for partition in set_partitions(STUBS)
        if all(sum(stub in FIFTH_STUBS for stub in block) <= 1 for block in partition)
    }
    ordered = tuple(sorted(result))
    distribution = Counter(len(representative) for representative in ordered)
    if ordered != EXPECTED_REPRESENTATIVES:
        raise AssertionError("branch-19 cross-pattern representative catalog changed")
    if distribution != EXPECTED_NONZERO_ROW_DISTRIBUTION:
        raise AssertionError("branch-19 nonzero-row distribution changed")
    return ordered


def lexicographic_pattern_key(pattern: int) -> tuple[bool, ...]:
    return tuple(bool(pattern & (1 << index)) for index in range(len(NEIGHBORS)))


def ordered_exterior_patterns(child: int) -> tuple[int, ...]:
    catalog = representatives()
    if not 0 <= child < len(catalog):
        raise ValueError("cross-pattern child outside range")
    representative = catalog[child]
    patterns = (0,) * (len(EXTERIOR) - len(representative)) + representative
    return tuple(sorted(patterns, key=lexicographic_pattern_key))


def cross_pattern_units(cnf, child: int) -> list[int]:
    units: list[int] = []
    for exterior, pattern in zip(EXTERIOR, ordered_exterior_patterns(child), strict=True):
        for index, neighbor in enumerate(NEIGHBORS):
            variable = edge_variable(cnf, neighbor, exterior)
            units.append(variable if pattern & (1 << index) else -variable)
    return units


def build_child(child: int):
    cnf = build_e040()
    for literal in cross_pattern_units(cnf, child):
        cnf.add(literal)
    return cnf


def render(child: int, path: Path) -> tuple[int, int, tuple[int, ...]]:
    catalog = representatives()
    if neighborhood_representatives()[BRANCH] != 183:
        raise AssertionError("E040 neighborhood branch is no longer K4 plus isolate")
    cnf = build_child(child)
    representative = catalog[child]
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 E042 branch-19 exact cross-pattern child, version 1\n")
        stream.write(
            f"c parent_branch={BRANCH} child={child:02d} "
            f"nonzero_patterns={','.join(map(str, representative))}\n"
        )
        stream.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    return cnf.variables, len(cnf.clauses), representative


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--child", type=int, choices=range(20), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, representative = render(args.child, args.output)
    print(
        "R5-BROOKS-BRANCH19-CROSS-PATTERN-CNF-PASS "
        f"child={args.child:02d} orbits=20 nonzero_rows={len(representative)} "
        f"variables={variables} clauses={clauses} fixed_cross_edges=100"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

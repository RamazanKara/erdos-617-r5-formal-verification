#!/usr/bin/env python3
"""Generate fixed-exceptional necessary CNFs at the local-count frontier.

The exceptional color is 0.  Its graph on B_0 is the complement of one
Kang--Pikhurko extremal non-4-partite K_5-free graph.  Colors 1,...,4 attain
their Turan bounds and are represented by four monochromatic clique blocks.
"""

from __future__ import annotations

import argparse
import itertools
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class CNF:
    variables: int = 0
    clauses: list[list[int]] = field(default_factory=list)
    names: dict[tuple[object, ...], int] = field(default_factory=dict)

    def variable(self, *name: object) -> int:
        key = tuple(name)
        if key not in self.names:
            self.variables += 1
            self.names[key] = self.variables
        return self.names[key]

    def add(self, *literals: int) -> None:
        if not literals:
            raise ValueError("generator attempted to add an empty clause")
        self.clauses.append(list(literals))

    def exactly_one(self, literals: list[int]) -> None:
        self.add(*literals)
        for left, right in itertools.combinations(literals, 2):
            self.add(-left, -right)

    def exactly_k(self, literals: list[int], bound: int, label: tuple[object, ...]) -> None:
        """Full unary dynamic-programming encoding of sum(literals) == bound."""
        if not 0 <= bound <= len(literals):
            raise ValueError("cardinality bound outside range")
        if bound == 0:
            for literal in literals:
                self.add(-literal)
            return
        if bound == len(literals):
            for literal in literals:
                self.add(literal)
            return

        limit = bound + 1
        counter: dict[tuple[int, int], int] = {}
        for index, literal in enumerate(literals, start=1):
            for count in range(1, min(index, limit) + 1):
                current = self.variable("counter", *label, index, count)
                counter[index, count] = current
                previous_same = counter.get((index - 1, count))
                if count == 1:
                    # current <-> previous_same or literal
                    if previous_same is not None:
                        self.add(-previous_same, current)
                        self.add(-current, previous_same, literal)
                    else:
                        self.add(-current, literal)
                    self.add(-literal, current)
                else:
                    previous_lower = counter[index - 1, count - 1]
                    # current <-> previous_same or (previous_lower and literal)
                    if previous_same is not None:
                        self.add(-previous_same, current)
                        self.add(-current, previous_same, previous_lower)
                        self.add(-current, previous_same, literal)
                    else:
                        self.add(-current, previous_lower)
                        self.add(-current, literal)
                    self.add(-previous_lower, -literal, current)

        self.add(counter[len(literals), bound])
        self.add(-counter[len(literals), bound + 1])

    def at_most_k(self, literals: list[int], bound: int, label: tuple[object, ...]) -> None:
        """Full unary dynamic-programming encoding of sum(literals) <= bound."""
        if not 0 <= bound <= len(literals):
            raise ValueError("cardinality bound outside range")
        if bound == len(literals):
            return
        if bound == 0:
            for literal in literals:
                self.add(-literal)
            return

        limit = bound + 1
        counter: dict[tuple[int, int], int] = {}
        for index, literal in enumerate(literals, start=1):
            for count in range(1, min(index, limit) + 1):
                current = self.variable("at-most-counter", *label, index, count)
                counter[index, count] = current
                previous_same = counter.get((index - 1, count))
                if count == 1:
                    if previous_same is not None:
                        self.add(-previous_same, current)
                        self.add(-current, previous_same, literal)
                    else:
                        self.add(-current, literal)
                    self.add(-literal, current)
                else:
                    previous_lower = counter[index - 1, count - 1]
                    if previous_same is not None:
                        self.add(-previous_same, current)
                        self.add(-current, previous_same, previous_lower)
                        self.add(-current, previous_same, literal)
                    else:
                        self.add(-current, previous_lower)
                        self.add(-current, literal)
                    self.add(-previous_lower, -literal, current)

        self.add(-counter[len(literals), bound + 1])

    def lexicographic_leq(
        self,
        first: list[int],
        second: list[int],
        label: tuple[object, ...],
    ) -> None:
        """Enforce first <= second for equal-length binary vectors."""
        if len(first) != len(second):
            raise ValueError("lexicographic vectors have different lengths")
        prefix_equal: int | None = None  # None denotes the constant true.
        for position, (left, right) in enumerate(zip(first, second, strict=True)):
            current = self.variable("lex-prefix", *label, position)
            if prefix_equal is None:
                self.add(-left, right)
                self.add(-current, -left, right)
                self.add(-current, left, -right)
                self.add(-left, -right, current)
                self.add(left, right, current)
            else:
                self.add(-prefix_equal, -left, right)
                self.add(-current, prefix_equal)
                self.add(-current, -left, right)
                self.add(-current, left, -right)
                self.add(-prefix_equal, -left, -right, current)
                self.add(-prefix_equal, left, right, current)
            prefix_equal = current

def exceptional_color_edges(
    parts: tuple[int, int, int, int], source: int, target: int, subset_size: int
) -> set[tuple[int, int]]:
    """Complement edges of the canonical Kang--Pikhurko G(parts) graph."""
    if source == target or not 0 <= source < 4 or not 0 <= target < 4:
        raise ValueError("source and target must be distinct part indices")
    if not 1 <= subset_size < parts[source]:
        raise ValueError("the distinguished subset must be nonempty and proper")

    blocks: list[list[int]] = []
    cursor = 0
    for size in parts:
        blocks.append(list(range(cursor, cursor + size)))
        cursor += size
    special = cursor
    subset = set(blocks[source][:subset_size])
    distinguished = blocks[target][0]

    edges: set[tuple[int, int]] = set()
    for block in blocks:
        edges.update(itertools.combinations(block, 2))
    for vertex in blocks[source]:
        if vertex not in subset:
            edges.add(tuple(sorted((special, vertex))))
    for vertex in blocks[target]:
        if vertex != distinguished:
            edges.add(tuple(sorted((special, vertex))))
    for vertex in subset:
        edges.add(tuple(sorted((distinguished, vertex))))
    return edges


def validate_parameters(
    case: str,
    parts: tuple[int, int, int, int],
    source: int,
    target: int,
) -> tuple[int, tuple[int, int, int, int]]:
    if tuple(sorted(parts)) != parts:
        raise ValueError("part vector must be nondecreasing")
    if {source, target} != {0, 1}:
        raise ValueError("source and target must be the first two eligible parts")
    if case == "balanced":
        if parts not in ((4, 4, 5, 6), (4, 5, 5, 5)):
            raise ValueError("unsupported balanced extremal part vector")
        if parts[source] not in (4, 5) or parts[target] not in (4, 5):
            raise ValueError("distinguished parts are not two smallest eligible parts")
        return 20, (5, 5, 5, 5)
    if case == "unbalanced":
        if parts != (4, 4, 5, 5) or {source, target} != {0, 1}:
            raise ValueError("unsupported unbalanced extremal parameters")
        return 19, (4, 5, 5, 5)
    if case == "l205":
        if parts not in ((4, 4, 6, 6), (4, 5, 5, 6), (5, 5, 5, 5)):
            raise ValueError("unsupported local-205 extremal part vector")
        return 21, (5, 5, 5, 6)
    if case in ("l206a", "l206b"):
        if parts not in ((4, 5, 6, 6), (5, 5, 5, 6)):
            raise ValueError("unsupported local-206 extremal part vector")
        group_sizes = (5, 5, 5, 7) if case == "l206a" else (5, 5, 6, 6)
        return 22, group_sizes
    if case == "l207slack":
        if parts not in ((4, 5, 6, 6), (5, 5, 5, 6)):
            raise ValueError("unsupported local-207 slack extremal part vector")
        return 22, (5, 5, 5, 7)
    if case in ("l207a", "l207b", "l207c"):
        if parts != (5, 5, 6, 6):
            raise ValueError("unsupported local-207 order-23 extremal part vector")
        group_sizes = {
            "l207a": (5, 5, 5, 8),
            "l207b": (5, 5, 6, 7),
            "l207c": (5, 6, 6, 6),
        }[case]
        return 23, group_sizes
    raise ValueError(
        "case must be balanced, unbalanced, l205, l206a, l206b, "
        "l207slack, l207a, l207b, or l207c"
    )


def representative_cases() -> list[
    tuple[str, str, tuple[int, int, int, int], int, int, int]
]:
    """Eight representatives; subset sizes a and |source|-a are isomorphic."""
    return [
        ("b4456_a1", "balanced", (4, 4, 5, 6), 0, 1, 1),
        ("b4456_a2", "balanced", (4, 4, 5, 6), 0, 1, 2),
        ("b4555_small_a1", "balanced", (4, 5, 5, 5), 0, 1, 1),
        ("b4555_small_a2", "balanced", (4, 5, 5, 5), 0, 1, 2),
        ("b4555_large_a1", "balanced", (4, 5, 5, 5), 1, 0, 1),
        ("b4555_large_a2", "balanced", (4, 5, 5, 5), 1, 0, 2),
        ("u4455_a1", "unbalanced", (4, 4, 5, 5), 0, 1, 1),
        ("u4455_a2", "unbalanced", (4, 4, 5, 5), 0, 1, 2),
    ]


def local_205_cases() -> list[
    tuple[str, str, tuple[int, int, int, int], int, int, int]
]:
    """Eight order-21 representatives for equality in the improved L=205 bound."""
    return [
        ("l205_4466_a1", "l205", (4, 4, 6, 6), 0, 1, 1),
        ("l205_4466_a2", "l205", (4, 4, 6, 6), 0, 1, 2),
        ("l205_4556_small_a1", "l205", (4, 5, 5, 6), 0, 1, 1),
        ("l205_4556_small_a2", "l205", (4, 5, 5, 6), 0, 1, 2),
        ("l205_4556_large_a1", "l205", (4, 5, 5, 6), 1, 0, 1),
        ("l205_4556_large_a2", "l205", (4, 5, 5, 6), 1, 0, 2),
        ("l205_5555_a1", "l205", (5, 5, 5, 5), 0, 1, 1),
        ("l205_5555_a2", "l205", (5, 5, 5, 5), 0, 1, 2),
    ]


def local_206_cases() -> list[
    tuple[str, str, tuple[int, int, int, int], int, int, int]
]:
    """Twelve order-22 representatives for the two arithmetic L=206 profiles."""
    cases: list[
        tuple[str, str, tuple[int, int, int, int], int, int, int]
    ] = []
    for profile, case in (("35557", "l206a"), ("35566", "l206b")):
        cases.extend(
            [
                (
                    f"l206_{profile}_4566_small_a1",
                    case,
                    (4, 5, 6, 6),
                    0,
                    1,
                    1,
                ),
                (
                    f"l206_{profile}_4566_small_a2",
                    case,
                    (4, 5, 6, 6),
                    0,
                    1,
                    2,
                ),
                (
                    f"l206_{profile}_4566_large_a1",
                    case,
                    (4, 5, 6, 6),
                    1,
                    0,
                    1,
                ),
                (
                    f"l206_{profile}_4566_large_a2",
                    case,
                    (4, 5, 6, 6),
                    1,
                    0,
                    2,
                ),
                (
                    f"l206_{profile}_5556_a1",
                    case,
                    (5, 5, 5, 6),
                    0,
                    1,
                    1,
                ),
                (
                    f"l206_{profile}_5556_a2",
                    case,
                    (5, 5, 5, 6),
                    0,
                    1,
                    2,
                ),
            ]
        )
    return cases


def local_207_fixed_cases() -> list[
    tuple[str, str, tuple[int, int, int, int], int, int, int]
]:
    """Six order-22 slack and six exact order-23 representatives."""
    cases: list[
        tuple[str, str, tuple[int, int, int, int], int, int, int]
    ] = []
    for parts, orientation in (
        ((4, 5, 6, 6), "small"),
        ((4, 5, 6, 6), "large"),
        ((5, 5, 5, 6), "equal"),
    ):
        source, target = (0, 1) if orientation != "large" else (1, 0)
        for subset_size in (1, 2):
            cases.append(
                (
                    f"l207_35557_slack_{''.join(map(str, parts))}_"
                    f"{orientation}_a{subset_size}",
                    "l207slack",
                    parts,
                    source,
                    target,
                    subset_size,
                )
            )
    for profile, case in (
        ("25558", "l207a"),
        ("25567", "l207b"),
        ("25666", "l207c"),
    ):
        for subset_size in (1, 2):
            cases.append(
                (
                    f"l207_{profile}_5566_a{subset_size}",
                    case,
                    (5, 5, 6, 6),
                    0,
                    1,
                    subset_size,
                )
            )
    return cases


def build_instance(
    case: str,
    parts: tuple[int, int, int, int],
    source: int,
    target: int,
    subset_size: int,
) -> tuple[CNF, dict[str, object]]:
    exceptional_order, group_sizes = validate_parameters(case, parts, source, target)
    if sum(parts) + 1 != exceptional_order:
        raise ValueError("part vector has the wrong order")
    exceptional_edges = exceptional_color_edges(parts, source, target, subset_size)
    expected_edges = {
        "balanced": 44,
        "unbalanced": 39,
        "l205": 49,
        "l206a": 54,
        "l206b": 54,
        "l207slack": 54,
        "l207a": 59,
        "l207b": 59,
        "l207c": 59,
    }[case]
    if len(exceptional_edges) != expected_edges:
        raise AssertionError("unexpected exceptional-color edge count")

    cnf = CNF()
    points = tuple(range(25))
    graph_points = tuple(range(exceptional_order))
    fixed_group_zero = tuple(range(exceptional_order, 25))
    tight_colors = (1, 2, 3, 4)

    group = {
        (point, color): cnf.variable("group", point, color)
        for point in graph_points
        for color in tight_colors
    }
    block = {
        (color, label, point): cnf.variable("block", color, label, point)
        for color in tight_colors
        for label in range(4)
        for point in points
    }

    # The exceptional graph vertices form the four nonzero spoke groups.
    for point in graph_points:
        cnf.exactly_one([group[point, color] for color in tight_colors])
    for color, size in zip(tight_colors, group_sizes, strict=True):
        cnf.exactly_k(
            [group[point, color] for point in graph_points],
            size,
            ("group-size", color),
        )
    if case == "balanced":
        # The four nonexceptional colors have identical roles, so the group
        # containing exceptional-graph vertex 0 may be named group 1.
        cnf.add(group[0, 1])
    # Equal-sized nonexceptional colors may be named by increasing least spoke
    # point.  In the unbalanced case color 1 has its unique size and colors
    # 2,3,4 remain interchangeable.
    interchangeable_classes = {
        "balanced": ((1, 2, 3, 4),),
        "unbalanced": ((2, 3, 4),),
        "l205": ((1, 2, 3),),
        "l206a": ((1, 2, 3),),
        "l206b": ((1, 2), (3, 4)),
        "l207slack": ((1, 2, 3),),
        "l207a": ((1, 2, 3),),
        "l207b": ((1, 2),),
        "l207c": ((2, 3, 4),),
    }[case]
    for interchangeable in interchangeable_classes:
        for first_color, second_color in zip(
            interchangeable, interchangeable[1:]
        ):
            for point in graph_points:
                cnf.add(
                    -group[point, second_color],
                    *[group[earlier, first_color] for earlier in range(point)],
                )

    # Vertices with identical closed neighborhoods in the fixed exceptional
    # graph are true twins.  Sort their complete group/block signatures;
    # simultaneous point permutation in every resolution proves this complete.
    closed_neighborhood = [set((point,)) for point in graph_points]
    for left, right in exceptional_edges:
        closed_neighborhood[left].add(right)
        closed_neighborhood[right].add(left)
    twin_classes: dict[tuple[int, ...], list[int]] = {}
    for point, neighborhood in enumerate(closed_neighborhood):
        twin_classes.setdefault(tuple(sorted(neighborhood)), []).append(point)
    for twins in twin_classes.values():
        for first_point, second_point in zip(twins, twins[1:]):
            for first_color in tight_colors:
                for second_color in tight_colors:
                    if first_color > second_color:
                        cnf.add(
                            -group[first_point, first_color],
                            -group[second_point, second_color],
                        )
            first_signature = [
                group[first_point, color] for color in reversed(tight_colors)
            ]
            second_signature = [
                group[second_point, color] for color in reversed(tight_colors)
            ]
            for color in tight_colors:
                first_signature.extend(
                    block[color, label, first_point] for label in reversed(range(4))
                )
                second_signature.extend(
                    block[color, label, second_point] for label in reversed(range(4))
                )
            cnf.lexicographic_leq(
                first_signature,
                second_signature,
                ("true-twin-signature", first_point, second_point),
            )
    # Resolution c partitions precisely the points outside spoke group A_c.
    for color in tight_colors:
        for point in graph_points:
            memberships = [block[color, label, point] for label in range(4)]
            cnf.add(group[point, color], *memberships)
            for membership in memberships:
                cnf.add(-group[point, color], -membership)
            for left, right in itertools.combinations(memberships, 2):
                cnf.add(-left, -right)
        for point in fixed_group_zero:
            cnf.exactly_one(
                [block[color, label, point] for label in range(4)]
            )

    # Fix the position of every uniquely sized block, then order equal-sized
    # block labels by their least point.  Every block is nonempty, so this keeps
    # exactly one labeling of each unordered block family.
    block_size_catalog: dict[int, tuple[int, int, int, int]] = {}
    for color, spoke_size in zip(tight_colors, group_sizes, strict=True):
        order = 25 - spoke_size
        quotient, remainder = divmod(order, 4)
        block_sizes = [quotient + 1] * remainder + [quotient] * (4 - remainder)
        if case == "l207slack" and color == 4:
            block_sizes = [5, 5, 5, 3]
        block_size_catalog[color] = tuple(block_sizes)
        for label, size in enumerate(block_sizes):
            cnf.exactly_k(
                [block[color, label, point] for point in points],
                size,
                ("block-size", color, label),
            )
        if case == "balanced":
            if color == 1:
                # Composition below labels block 0 by its doubled A_0 group.
                # The A_0 points are otherwise freely permutable.
                cnf.add(block[color, 0, fixed_group_zero[0]])
                cnf.add(block[color, 0, fixed_group_zero[1]])
                cnf.add(block[color, 1, fixed_group_zero[2]])
                cnf.add(block[color, 2, fixed_group_zero[3]])
                cnf.add(block[color, 3, fixed_group_zero[4]])
            continue
        for size in sorted(set(block_sizes), reverse=True):
            equal_labels = [
                label for label, block_size in enumerate(block_sizes)
                if block_size == size
            ]
            for first_label, second_label in zip(equal_labels, equal_labels[1:]):
                for point in points:
                    cnf.add(
                        -block[color, second_label, point],
                        *[block[color, first_label, earlier] for earlier in range(point)],
                    )

    if case == "balanced":
        # Every tight block meets A_0 because alpha(G_0) <= 4, and it meets
        # every other available spoke group by the cross-resolution capacity
        # argument.  Its four positive group intersections sum to five, so its
        # composition is (2,1,1,1); each group is doubled once per resolution.
        for color in tight_colors:
            available_groups = [0] + [
                other for other in tight_colors if other != color
            ]
            for label, doubled_group in enumerate(available_groups):
                for point_group in available_groups:
                    if point_group == 0:
                        intersections = [
                            block[color, label, point]
                            for point in fixed_group_zero
                        ]
                    else:
                        intersections = []
                        for point in graph_points:
                            membership = cnf.variable(
                                "block-group-intersection",
                                color,
                                label,
                                point_group,
                                point,
                            )
                            cnf.add(-membership, block[color, label, point])
                            cnf.add(-membership, group[point, point_group])
                            cnf.add(
                                -block[color, label, point],
                                -group[point, point_group],
                                membership,
                            )
                            intersections.append(membership)
                    cnf.exactly_k(
                        intersections,
                        2 if point_group == doubled_group else 1,
                        ("block-group-size", color, label, point_group),
                    )

    # A point pair cannot lie in monochromatic clique blocks of two colors.
    for first, second in itertools.combinations(tight_colors, 2):
        for first_label in range(4):
            for second_label in range(4):
                for left, right in itertools.combinations(points, 2):
                    cnf.add(
                        -block[first, first_label, left],
                        -block[first, first_label, right],
                        -block[second, second_label, left],
                        -block[second, second_label, right],
                    )

    # Every edge already forced to exceptional color 0 is forbidden inside all
    # tight-color clique blocks.
    for left, right in sorted(exceptional_edges):
        for color in tight_colors:
            for label in range(4):
                cnf.add(-block[color, label, left], -block[color, label, right])

    metadata: dict[str, object] = {
        "case": case,
        "parts": parts,
        "source": source,
        "target": target,
        "subset_size": subset_size,
        "exceptional_order": exceptional_order,
        "exceptional_edges": exceptional_edges,
        "group_sizes": group_sizes,
        "group_variables": group,
        "block_variables": block,
        "block_sizes": block_size_catalog,
    }
    return cnf, metadata


def render(
    case: str,
    parts: tuple[int, int, int, int],
    source: int,
    target: int,
    subset_size: int,
) -> str:
    cnf, metadata = build_instance(case, parts, source, target, subset_size)
    lines = [
        (
            "c ERDOS617 local "
            f"L={'207' if case.startswith('l207') else '206' if case in ('l206a', 'l206b') else '205' if case == 'l205' else '204'} "
            "compatibility, version 1"
        ),
        (
            f"c case={case} parts={','.join(map(str, parts))} source={source} "
            f"target={target} subset_size={subset_size}"
        ),
        f"c exceptional_color_edges={len(metadata['exceptional_edges'])}",
        f"p cnf {cnf.variables} {len(cnf.clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in cnf.clauses)
    return "\n".join(lines) + "\n"


def parse_parts(text: str) -> tuple[int, int, int, int]:
    fields = tuple(map(int, text.split(",")))
    if len(fields) != 4:
        raise argparse.ArgumentTypeError("expected four comma-separated part sizes")
    return fields


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--case",
        choices=(
            "balanced",
            "unbalanced",
            "l205",
            "l206a",
            "l206b",
            "l207slack",
            "l207a",
            "l207b",
            "l207c",
        ),
        required=True,
    )
    parser.add_argument("--parts", type=parse_parts, required=True)
    parser.add_argument("--source", type=int, required=True)
    parser.add_argument("--target", type=int, required=True)
    parser.add_argument("--subset-size", type=int, required=True)
    args = parser.parse_args()
    args.output.write_text(
        render(args.case, args.parts, args.source, args.target, args.subset_size),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

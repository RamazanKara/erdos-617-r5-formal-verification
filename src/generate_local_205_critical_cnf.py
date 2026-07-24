#!/usr/bin/env python3
"""Generate necessary CNFs for exact-component critical E009 branches.

The exceptional color graph has 20 vertices, independence number four, and is
edge-critical.  Componentwise Kang--Pikhurko bounds leave two zero-slack
component profiles.  In these instances the exceptional graph is fixed and
the four spoke groups and tight resolutions remain variable.
"""

from __future__ import annotations

import argparse
import itertools
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_204_cnf import CNF  # noqa: E402


Case = tuple[str, str, tuple[int, ...], int, int, int]


def component_complement_edges(
    parts: tuple[int, ...], source: int, target: int, subset_size: int
) -> set[tuple[int, int]]:
    """Complement edges of a canonical Kang--Pikhurko component."""
    if source == target or not 0 <= source < len(parts) or not 0 <= target < len(parts):
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


def critical_exact_cases() -> list[Case]:
    """Eight representatives for the two zero-slack component profiles."""
    return [
        ("c112_55_a1", "112", (5, 5), 0, 1, 1),
        ("c112_55_a2", "112", (5, 5), 0, 1, 2),
        ("c13_456_small_a1", "13", (4, 5, 6), 0, 1, 1),
        ("c13_456_small_a2", "13", (4, 5, 6), 0, 1, 2),
        ("c13_456_large_a1", "13", (4, 5, 6), 1, 0, 1),
        ("c13_456_large_a2", "13", (4, 5, 6), 1, 0, 2),
        ("c13_555_a1", "13", (5, 5, 5), 0, 1, 1),
        ("c13_555_a2", "13", (5, 5, 5), 0, 1, 2),
    ]


def fixed_exceptional_edges(
    profile: str,
    parts: tuple[int, ...],
    source: int,
    target: int,
    subset_size: int,
) -> set[tuple[int, int]]:
    """Build the complete 20-vertex exceptional graph for one case."""
    component = component_complement_edges(parts, source, target, subset_size)
    if profile == "112":
        if parts != (5, 5) or len(component) != 29:
            raise ValueError("invalid alpha profile (1,1,2) component")
        edges = set(component)
        edges.update(itertools.combinations(range(11, 15), 2))
        edges.update(itertools.combinations(range(15, 20), 2))
    elif profile == "13":
        if parts not in ((4, 5, 6), (5, 5, 5)) or len(component) != 39:
            raise ValueError("invalid alpha profile (1,3) component")
        edges = set(component)
        edges.update(itertools.combinations(range(16, 20), 2))
    else:
        raise ValueError("profile must be '112' or '13'")
    if len(edges) != 45:
        raise AssertionError("critical exact graph must have 45 edges")
    return edges


def build_fixed_balanced_instance(
    exceptional_edges: set[tuple[int, int]],
    *,
    cnf: CNF | None = None,
    variable_exceptional_edges: dict[tuple[int, int], int] | None = None,
) -> tuple[CNF, dict[str, object]]:
    """Encode balanced spoke assignments and four exact tight resolutions."""
    if cnf is None:
        cnf = CNF()
    if variable_exceptional_edges is None:
        variable_exceptional_edges = {}
    if exceptional_edges & variable_exceptional_edges.keys():
        raise ValueError("an exceptional edge cannot be both fixed and variable")
    points = tuple(range(25))
    graph_points = tuple(range(20))
    fixed_group_zero = tuple(range(20, 25))
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

    for point in graph_points:
        cnf.exactly_one([group[point, color] for color in tight_colors])
    for color in tight_colors:
        cnf.exactly_k(
            [group[point, color] for point in graph_points],
            5,
            ("group-size", color),
        )

    # The nonexceptional colors have equal roles.  Name the group containing
    # point 0 first, then name the remaining groups by increasing least point.
    cnf.add(group[0, 1])
    for first_color, second_color in zip(tight_colors, tight_colors[1:]):
        for point in graph_points:
            cnf.add(
                -group[point, second_color],
                *[group[earlier, first_color] for earlier in range(point)],
            )

    # Closed-neighborhood twins can be ordered by their complete incidence
    # signatures.  These permutations are automorphisms of the fixed graph.
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
                    block[color, label, first_point]
                    for label in reversed(range(4))
                )
                second_signature.extend(
                    block[color, label, second_point]
                    for label in reversed(range(4))
                )
            cnf.lexicographic_leq(
                first_signature,
                second_signature,
                ("true-twin-signature", first_point, second_point),
            )

    # Resolution c partitions exactly the points outside spoke group A_c.
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

    for color in tight_colors:
        for label in range(4):
            cnf.exactly_k(
                [block[color, label, point] for point in points],
                5,
                ("block-size", color, label),
            )
        if color == 1:
            cnf.add(block[color, 0, fixed_group_zero[0]])
            cnf.add(block[color, 0, fixed_group_zero[1]])
            cnf.add(block[color, 1, fixed_group_zero[2]])
            cnf.add(block[color, 2, fixed_group_zero[3]])
            cnf.add(block[color, 3, fixed_group_zero[4]])

    # Every tight block has group composition (2,1,1,1), and each available
    # group is doubled once in each resolution.
    for color in tight_colors:
        available_groups = [0] + [
            other for other in tight_colors if other != color
        ]
        for label, doubled_group in enumerate(available_groups):
            for point_group in available_groups:
                if point_group == 0:
                    intersections = [
                        block[color, label, point] for point in fixed_group_zero
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

    for left, right in sorted(exceptional_edges):
        for color in tight_colors:
            for label in range(4):
                cnf.add(-block[color, label, left], -block[color, label, right])
    for (left, right), edge in sorted(variable_exceptional_edges.items()):
        for color in tight_colors:
            for label in range(4):
                cnf.add(
                    -edge,
                    -block[color, label, left],
                    -block[color, label, right],
                )

    return cnf, {
        "exceptional_edges": exceptional_edges,
        "variable_exceptional_edges": variable_exceptional_edges,
        "group_variables": group,
        "block_variables": block,
        "twin_classes": tuple(tuple(value) for value in twin_classes.values()),
    }


def render(
    profile: str,
    parts: tuple[int, ...],
    source: int,
    target: int,
    subset_size: int,
) -> str:
    exceptional_edges = fixed_exceptional_edges(
        profile, parts, source, target, subset_size
    )
    cnf, _ = build_fixed_balanced_instance(exceptional_edges)
    lines = [
        "c ERDOS617 local L=205 edge-critical exact-component compatibility, version 1",
        (
            f"c profile={profile} parts={','.join(map(str, parts))} "
            f"source={source} target={target} subset_size={subset_size}"
        ),
        f"c exceptional_color_edges={len(exceptional_edges)}",
        f"p cnf {cnf.variables} {len(cnf.clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in cnf.clauses)
    return "\n".join(lines) + "\n"


def parse_parts(text: str) -> tuple[int, ...]:
    fields = tuple(map(int, text.split(",")))
    if len(fields) not in (2, 3):
        raise argparse.ArgumentTypeError("expected two or three comma-separated sizes")
    return fields


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--profile", choices=("112", "13"), required=True)
    parser.add_argument("--parts", type=parse_parts, required=True)
    parser.add_argument("--source", type=int, required=True)
    parser.add_argument("--target", type=int, required=True)
    parser.add_argument("--subset-size", type=int, required=True)
    args = parser.parse_args()
    args.output.write_text(
        render(
            args.profile,
            args.parts,
            args.source,
            args.target,
            args.subset_size,
        ),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Generate the E014 mixed-order two-exception CNF."""

from __future__ import annotations

import argparse
import itertools
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_204_cnf import CNF  # noqa: E402
from src.generate_local_208_double_cnf import (  # noqa: E402
    fix_complete_resolution,
    fix_free_group,
)


CASE = "unbalanced_double49_44"
GROUPS = {
    0: tuple(range(21, 25)),
    1: tuple(range(0, 5)),
    2: tuple(range(5, 10)),
    3: tuple(range(10, 15)),
    4: tuple(range(15, 21)),
}
EXCEPTIONAL_COLORS = (0, 1)
TIGHT_COLORS = (2, 3, 4)
EDGE_COUNTS = {0: 49, 1: 44}
FORCED_ROLES = {
    2: (1, 3, 4, 4),
    3: (1, 2, 4, 4),
}


def build_instance(
    require_edge_minimality: bool = False,
    fix_second_resolution_free_group: bool = False,
    edge_minimality_colors: tuple[int, ...] | None = None,
) -> tuple[CNF, dict[str, object]]:
    points = tuple(range(25))
    graph_points = {
        color: tuple(point for point in points if point not in GROUPS[color])
        for color in EXCEPTIONAL_COLORS
    }
    if require_edge_minimality and edge_minimality_colors is not None:
        raise ValueError("use either all-color or selective edge minimality")
    minimality_colors = set(
        EXCEPTIONAL_COLORS if require_edge_minimality else ()
    )
    if edge_minimality_colors is not None:
        minimality_colors = set(edge_minimality_colors)
        if not minimality_colors <= set(EXCEPTIONAL_COLORS):
            raise ValueError("edge-minimality override has wrong colors")
    cnf = CNF()
    block = {
        (color, label, point): cnf.variable("block", color, label, point)
        for color in TIGHT_COLORS
        for label in range(4)
        for point in points
    }
    exceptional = {
        (color, left, right): cnf.variable(
            "exceptional-edge", color, left, right
        )
        for color in EXCEPTIONAL_COLORS
        for left, right in itertools.combinations(graph_points[color], 2)
    }

    for color in TIGHT_COLORS:
        for point in points:
            memberships = [block[color, label, point] for label in range(4)]
            if point in GROUPS[color]:
                for membership in memberships:
                    cnf.add(-membership)
            else:
                cnf.exactly_one(memberships)
        order = 25 - len(GROUPS[color])
        quotient, remainder = divmod(order, 4)
        block_sizes = [quotient + 1] * remainder + [quotient] * (4 - remainder)
        for label, size in enumerate(block_sizes):
            cnf.exactly_k(
                [block[color, label, point] for point in points],
                size,
                ("block-size", color, label),
            )

    # The four size-five blocks in colors 2 and 3 meet every available spoke
    # group.  Their group-size surpluses force the listed doubled groups.
    for color, roles in FORCED_ROLES.items():
        for label, doubled_group in enumerate(roles):
            for point_group in range(5):
                if point_group == color:
                    continue
                cnf.exactly_k(
                    [
                        block[color, label, point]
                        for point in GROUPS[point_group]
                    ],
                    2 if point_group == doubled_group else 1,
                    ("block-group-size", color, label, point_group),
                )

    # Color 4 has three size-five blocks and one size-four block.  Each
    # size-five block necessarily meets every available spoke group, but the
    # doubled groups are not fixed because the size-four block's composition
    # need not be (1,1,1,1).  Keep the complete union as one relaxation.
    positive_group_intersections = 0
    for label in range(3):
        for point_group in (0, 1, 2, 3):
            cnf.add(
                *[
                    block[4, label, point]
                    for point in GROUPS[point_group]
                ]
            )
            positive_group_intersections += 1

    fixed_resolution_memberships = fix_complete_resolution(
        cnf,
        block,
        GROUPS,
        2,
        FORCED_ROLES[2],
    )
    fixed_free_group_memberships = 0
    if fix_second_resolution_free_group:
        fixed_free_group_memberships = fix_free_group(
            cnf,
            block,
            GROUPS,
            2,
            3,
            FORCED_ROLES[3],
        )

    # Equal forced roles in colors 2 and 3, and all three equal-size positive-
    # intersection roles in color 4, remain interchangeable.  Order each
    # label class by least point.
    equal_label_pairs = ((2, 2, 3), (3, 2, 3), (4, 0, 1), (4, 1, 2))
    equal_role_order_clauses = 0
    for color, first_label, second_label in equal_label_pairs:
        for point in points:
            cnf.add(
                -block[color, second_label, point],
                *[
                    block[color, first_label, earlier]
                    for earlier in range(point)
                ],
            )
            equal_role_order_clauses += 1

    cross_resolution_clauses = 0
    for first, second in itertools.combinations(TIGHT_COLORS, 2):
        for first_label in range(4):
            for second_label in range(4):
                for left, right in itertools.combinations(points, 2):
                    cnf.add(
                        -block[first, first_label, left],
                        -block[first, first_label, right],
                        -block[second, second_label, left],
                        -block[second, second_label, right],
                    )
                    cross_resolution_clauses += 1

    five_sets: dict[int, int] = {}
    six_sets: dict[int, int] = {}
    for color in EXCEPTIONAL_COLORS:
        color_edges = {
            (left, right): exceptional[color, left, right]
            for left, right in itertools.combinations(graph_points[color], 2)
        }
        cnf.exactly_k(
            list(color_edges.values()),
            EDGE_COUNTS[color],
            ("exceptional-edge-count", color),
        )
        five_sets[color] = 0
        for subset in itertools.combinations(graph_points[color], 5):
            cnf.add(
                *[
                    color_edges[pair]
                    for pair in itertools.combinations(subset, 2)
                ]
            )
            five_sets[color] += 1
        six_sets[color] = 0
        for subset in itertools.combinations(graph_points[color], 6):
            cnf.add(
                *[
                    -color_edges[pair]
                    for pair in itertools.combinations(subset, 2)
                ]
            )
            six_sets[color] += 1

    common_pairs = sorted(
        set(itertools.combinations(graph_points[0], 2))
        & set(itertools.combinations(graph_points[1], 2))
    )
    for left, right in common_pairs:
        cnf.add(
            -exceptional[0, left, right],
            -exceptional[1, left, right],
        )

    exceptional_block_clauses = 0
    for (color, left, right), edge in exceptional.items():
        for tight_color in TIGHT_COLORS:
            for label in range(4):
                cnf.add(
                    -edge,
                    -block[tight_color, label, left],
                    -block[tight_color, label, right],
                )
                exceptional_block_clauses += 1

    private_witness_selectors = {color: 0 for color in EXCEPTIONAL_COLORS}
    if minimality_colors:
        for color in EXCEPTIONAL_COLORS:
            if color not in minimality_colors:
                continue
            for left, right in itertools.combinations(graph_points[color], 2):
                edge = exceptional[color, left, right]
                remaining = [
                    point
                    for point in graph_points[color]
                    if point not in (left, right)
                ]
                selectors = [
                    cnf.variable(
                        "private-witness-vertex", color, left, right, point
                    )
                    for point in remaining
                ]
                private_witness_selectors[color] += len(selectors)
                first_gated_clause = len(cnf.clauses)
                cnf.exactly_k(
                    selectors,
                    3,
                    ("private-witness-size", color, left, right),
                )
                for clause in cnf.clauses[first_gated_clause:]:
                    clause.append(-edge)
                for point, selector in zip(remaining, selectors, strict=True):
                    cnf.add(-selector, edge)
                    cnf.add(
                        -selector,
                        -exceptional[color, *tuple(sorted((left, point)))],
                    )
                    cnf.add(
                        -selector,
                        -exceptional[color, *tuple(sorted((right, point)))],
                    )
                for first_index, second_index in itertools.combinations(
                    range(len(remaining)), 2
                ):
                    pair = tuple(
                        sorted((remaining[first_index], remaining[second_index]))
                    )
                    cnf.add(
                        -selectors[first_index],
                        -selectors[second_index],
                        -exceptional[color, *pair],
                    )

    return cnf, {
        "case": CASE,
        "groups": GROUPS,
        "exceptional_colors": EXCEPTIONAL_COLORS,
        "tight_colors": TIGHT_COLORS,
        "graph_points": graph_points,
        "exceptional_variables": {
            color: len(tuple(itertools.combinations(graph_points[color], 2)))
            for color in EXCEPTIONAL_COLORS
        },
        "exceptional_edge_counts": EDGE_COUNTS,
        "five_sets": five_sets,
        "six_sets": six_sets,
        "forced_roles": FORCED_ROLES,
        "positive_group_intersections": positive_group_intersections,
        "fixed_resolution_memberships": fixed_resolution_memberships,
        "fixed_free_group_memberships": fixed_free_group_memberships,
        "equal_role_order_clauses": equal_role_order_clauses,
        "cross_resolution_clauses": cross_resolution_clauses,
        "common_exceptional_pairs": len(common_pairs),
        "exceptional_block_clauses": exceptional_block_clauses,
        "private_witness_selectors": private_witness_selectors,
    }


def render(
    require_edge_minimality: bool = False,
    fix_second_resolution_free_group: bool = False,
) -> str:
    cnf, metadata = build_instance(
        require_edge_minimality,
        fix_second_resolution_free_group,
    )
    lines = [
        "c ERDOS617 local L=209 mixed-order two-exception compatibility, version 1",
        (
            "c case=unbalanced_double49_44 exceptional_colors=0,1 "
            "exceptional_orders=21,20 exceptional_edges=49,44 alpha<=4 omega<=5"
        ),
        (
            "c edge_minimality="
            f"{int(require_edge_minimality)} fixed_resolution_memberships="
            f"{metadata['fixed_resolution_memberships']} "
            "fixed_free_group_memberships="
            f"{metadata['fixed_free_group_memberships']} "
            "common_exceptional_pairs="
            f"{metadata['common_exceptional_pairs']}"
        ),
        f"p cnf {cnf.variables} {len(cnf.clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in cnf.clauses)
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--minimal", action="store_true")
    parser.add_argument("--fix-second-resolution-free-group", action="store_true")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(
        render(args.minimal, args.fix_second_resolution_free_group),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

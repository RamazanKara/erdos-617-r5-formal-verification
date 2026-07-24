#!/usr/bin/env python3
"""Generate classification-free two-exception CNFs at local count 208."""

from __future__ import annotations

import argparse
import itertools
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_204_cnf import CNF  # noqa: E402


def parameters(case: str):
    if case == "balanced_double44":
        return (
            {
                0: tuple(range(0, 5)),
                1: tuple(range(5, 10)),
                2: tuple(range(10, 15)),
                3: tuple(range(15, 20)),
                4: tuple(range(20, 25)),
            },
            (0, 1),
            (2, 3, 4),
            {0: 44, 1: 44},
        )
    if case == "unbalanced_double49_39":
        return (
            {
                0: tuple(range(21, 25)),
                1: tuple(range(0, 5)),
                2: tuple(range(5, 10)),
                3: tuple(range(10, 15)),
                4: tuple(range(15, 21)),
            },
            (0, 4),
            (1, 2, 3),
            {0: 49, 4: 39},
        )
    raise ValueError(f"unsupported local-208 double case {case!r}")


def doubled_groups(
    case: str, color: int, tight_colors: tuple[int, ...]
) -> tuple[int, int, int, int]:
    if case == "balanced_double44":
        return tuple(group for group in range(5) if group != color)  # type: ignore[return-value]
    other_tight = tuple(group for group in tight_colors if group != color)
    return (*other_tight, 4, 4)


def fix_complete_resolution(
    cnf: CNF,
    block: dict[tuple[int, int, int], int],
    groups: dict[int, tuple[int, ...]],
    color: int,
    roles: tuple[int, int, int, int],
) -> int:
    """Use independent permutations inside available groups to fix a resolution."""

    fixed = 0
    for point_group in range(5):
        if point_group == color:
            continue
        points = groups[point_group]
        doubled_labels = [
            label for label, doubled_group in enumerate(roles) if doubled_group == point_group
        ]
        singleton_labels = [label for label in range(4) if label not in doubled_labels]
        cursor = 0
        for label in doubled_labels:
            for point in points[cursor : cursor + 2]:
                cnf.add(block[color, label, point])
                fixed += 1
            cursor += 2
        for label, point in zip(singleton_labels, points[cursor:], strict=True):
            cnf.add(block[color, label, point])
            fixed += 1
    return fixed


def fix_free_group(
    cnf: CNF,
    block: dict[tuple[int, int, int], int],
    groups: dict[int, tuple[int, ...]],
    first_color: int,
    second_color: int,
    second_roles: tuple[int, int, int, int],
) -> int:
    """Name the still-free points excluded from the fixed first resolution."""

    points = groups[first_color]
    doubled_labels = [
        label
        for label, doubled_group in enumerate(second_roles)
        if doubled_group == first_color
    ]
    if len(points) != 5 or len(doubled_labels) != 1:
        raise AssertionError("free-group quotient requires multiplicities 2,1,1,1")
    doubled_label = doubled_labels[0]
    cnf.add(block[second_color, doubled_label, points[0]])
    cnf.add(block[second_color, doubled_label, points[1]])
    singleton_labels = [label for label in range(4) if label != doubled_label]
    for label, point in zip(singleton_labels, points[2:], strict=True):
        cnf.add(block[second_color, label, point])
    return 5


def build_instance(
    case: str,
    require_edge_minimality: bool = False,
    fix_second_resolution_free_group: bool = False,
    exceptional_edge_counts: dict[int, int] | None = None,
    edge_minimality_colors: tuple[int, ...] | None = None,
) -> tuple[CNF, dict[str, object]]:
    groups, exceptional_colors, tight_colors, edge_counts = parameters(case)
    if exceptional_edge_counts is not None:
        if set(exceptional_edge_counts) != set(exceptional_colors):
            raise ValueError("exceptional edge-count override has wrong colors")
        edge_counts = dict(exceptional_edge_counts)
    if require_edge_minimality and edge_minimality_colors is not None:
        raise ValueError("use either all-color or selective edge minimality")
    minimality_colors = set(
        exceptional_colors if require_edge_minimality else ()
    )
    if edge_minimality_colors is not None:
        minimality_colors = set(edge_minimality_colors)
        if not minimality_colors <= set(exceptional_colors):
            raise ValueError("edge-minimality override has wrong colors")
    points = tuple(range(25))
    graph_points = {
        color: tuple(point for point in points if point not in groups[color])
        for color in exceptional_colors
    }
    cnf = CNF()
    block = {
        (color, label, point): cnf.variable("block", color, label, point)
        for color in tight_colors
        for label in range(4)
        for point in points
    }
    exceptional = {
        (color, left, right): cnf.variable(
            "exceptional-edge", color, left, right
        )
        for color in exceptional_colors
        for left, right in itertools.combinations(graph_points[color], 2)
    }

    roles_by_color = {
        color: doubled_groups(case, color, tight_colors) for color in tight_colors
    }
    for color in tight_colors:
        for point in points:
            memberships = [block[color, label, point] for label in range(4)]
            if point in groups[color]:
                for membership in memberships:
                    cnf.add(-membership)
            else:
                cnf.exactly_one(memberships)
        for label in range(4):
            cnf.exactly_k(
                [block[color, label, point] for point in points],
                5,
                ("block-size", color, label),
            )
        for label, doubled_group in enumerate(roles_by_color[color]):
            for point_group in range(5):
                if point_group == color:
                    continue
                cnf.exactly_k(
                    [
                        block[color, label, point]
                        for point in groups[point_group]
                    ],
                    2 if point_group == doubled_group else 1,
                    ("block-group-size", color, label, point_group),
                )

    first_color = tight_colors[0]
    fixed_resolution_memberships = fix_complete_resolution(
        cnf,
        block,
        groups,
        first_color,
        roles_by_color[first_color],
    )
    fixed_free_group_memberships = 0
    if fix_second_resolution_free_group:
        fixed_free_group_memberships = fix_free_group(
            cnf,
            block,
            groups,
            first_color,
            tight_colors[1],
            roles_by_color[tight_colors[1]],
        )

    equal_role_order_clauses = 0
    if case == "unbalanced_double49_39":
        # The two A_4-doubled blocks in each tight resolution are the only
        # equal-role labels.  Order them by their least point.
        for color in tight_colors:
            for point in points:
                cnf.add(
                    -block[color, 3, point],
                    *[block[color, 2, earlier] for earlier in range(point)],
                )
                equal_role_order_clauses += 1

    cross_resolution_clauses = 0
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
                    cross_resolution_clauses += 1

    five_sets: dict[int, int] = {}
    six_sets: dict[int, int] = {}
    for color in exceptional_colors:
        color_edges = {
            (left, right): exceptional[color, left, right]
            for left, right in itertools.combinations(graph_points[color], 2)
        }
        cnf.exactly_k(
            list(color_edges.values()),
            edge_counts[color],
            ("exceptional-edge-count", color),
        )
        five_sets[color] = 0
        for subset in itertools.combinations(graph_points[color], 5):
            cnf.add(
                *[
                    color_edges[tuple(sorted((left, right)))]
                    for left, right in itertools.combinations(subset, 2)
                ]
            )
            five_sets[color] += 1
        six_sets[color] = 0
        for subset in itertools.combinations(graph_points[color], 6):
            cnf.add(
                *[
                    -color_edges[tuple(sorted((left, right)))]
                    for left, right in itertools.combinations(subset, 2)
                ]
            )
            six_sets[color] += 1

    common_pairs = sorted(
        set(itertools.combinations(graph_points[exceptional_colors[0]], 2))
        & set(itertools.combinations(graph_points[exceptional_colors[1]], 2))
    )
    for left, right in common_pairs:
        cnf.add(
            -exceptional[exceptional_colors[0], left, right],
            -exceptional[exceptional_colors[1], left, right],
        )

    exceptional_block_clauses = 0
    for (color, left, right), edge in exceptional.items():
        for tight_color in tight_colors:
            for label in range(4):
                cnf.add(
                    -edge,
                    -block[tight_color, label, left],
                    -block[tight_color, label, right],
                )
                exceptional_block_clauses += 1

    private_witness_selectors: dict[int, int] = {
        color: 0 for color in exceptional_colors
    }
    if minimality_colors:
        for color in exceptional_colors:
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
        "case": case,
        "groups": groups,
        "exceptional_colors": exceptional_colors,
        "tight_colors": tight_colors,
        "graph_points": graph_points,
        "exceptional_variables": {
            color: len(tuple(itertools.combinations(graph_points[color], 2)))
            for color in exceptional_colors
        },
        "exceptional_edge_counts": edge_counts,
        "five_sets": five_sets,
        "six_sets": six_sets,
        "roles_by_color": roles_by_color,
        "fixed_resolution_memberships": fixed_resolution_memberships,
        "fixed_free_group_memberships": fixed_free_group_memberships,
        "equal_role_order_clauses": equal_role_order_clauses,
        "cross_resolution_clauses": cross_resolution_clauses,
        "common_exceptional_pairs": len(common_pairs),
        "exceptional_block_clauses": exceptional_block_clauses,
        "private_witness_selectors": private_witness_selectors,
    }


def render(
    case: str,
    require_edge_minimality: bool = False,
    fix_second_resolution_free_group: bool = False,
) -> str:
    cnf, metadata = build_instance(
        case,
        require_edge_minimality,
        fix_second_resolution_free_group,
    )
    exceptional_colors = metadata["exceptional_colors"]
    edge_counts = metadata["exceptional_edge_counts"]
    orders = {
        color: len(metadata["graph_points"][color]) for color in exceptional_colors
    }
    lines = [
        "c ERDOS617 local L=208 two-exception compatibility, version 1",
        (
            f"c case={case} exceptional_colors="
            + ",".join(map(str, exceptional_colors))
            + " exceptional_orders="
            + ",".join(str(orders[color]) for color in exceptional_colors)
            + " exceptional_edges="
            + ",".join(str(edge_counts[color]) for color in exceptional_colors)
            + " alpha<=4 omega<=5"
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
    parser.add_argument(
        "--case",
        choices=("balanced_double44", "unbalanced_double49_39"),
        required=True,
    )
    parser.add_argument("--minimal", action="store_true")
    parser.add_argument("--fix-second-resolution-free-group", action="store_true")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(
        render(
            args.case,
            args.minimal,
            args.fix_second_resolution_free_group,
        ),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

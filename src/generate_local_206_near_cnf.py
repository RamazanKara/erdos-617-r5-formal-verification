#!/usr/bin/env python3
"""Generate classification-free necessary CNFs at local count 206."""

from __future__ import annotations

import argparse
import itertools
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_204_cnf import CNF  # noqa: E402
from src.generate_local_205_near_cnf import (  # noqa: E402
    build_instance as build_balanced_base,
)


def resolution_four_profiles() -> list[tuple[int, int, int, int]]:
    """All doubled-group count vectors for the three size-five blocks."""
    return [
        profile
        for profile in itertools.product(range(3), repeat=4)
        if sum(profile) == 3 and profile[0] <= 1
    ]


def build_unbalanced(
    require_edge_minimality: bool = False,
    require_forced_compositions: bool = False,
    resolution_four_profile: tuple[int, int, int, int] | None = None,
    fix_resolution_two_group_one: bool = False,
    exceptional_edge_count: int = 50,
) -> tuple[CNF, dict[str, object]]:
    """Profile (4,5,5,5,6), with a variable graph on B_0."""
    if exceptional_edge_count not in (50, 51, 52, 53):
        raise ValueError(
            "unbalanced exceptional edge count must be 50, 51, 52, or 53"
        )
    if resolution_four_profile is not None:
        if not require_forced_compositions:
            raise ValueError("resolution-four branching requires compositions")
        if resolution_four_profile not in resolution_four_profiles():
            raise ValueError("invalid resolution-four doubled-group profile")
    if fix_resolution_two_group_one and not require_forced_compositions:
        raise ValueError("resolution-two orbit fix requires compositions")
    cnf = CNF()
    points = tuple(range(25))
    tight_colors = (1, 2, 3, 4)
    groups = {
        0: tuple(range(21, 25)),
        1: tuple(range(0, 5)),
        2: tuple(range(5, 10)),
        3: tuple(range(10, 15)),
        4: tuple(range(15, 21)),
    }
    graph_points = tuple(range(21))

    block = {
        (color, label, point): cnf.variable("block", color, label, point)
        for color in tight_colors
        for label in range(4)
        for point in points
    }
    exceptional = {
        (left, right): cnf.variable("exceptional-edge", left, right)
        for left, right in itertools.combinations(graph_points, 2)
    }

    for color in tight_colors:
        for point in points:
            memberships = [block[color, label, point] for label in range(4)]
            if point in groups[color]:
                for membership in memberships:
                    cnf.add(-membership)
            else:
                cnf.exactly_one(memberships)

        order = 25 - len(groups[color])
        quotient, remainder = divmod(order, 4)
        block_sizes = [quotient + 1] * remainder + [quotient] * (4 - remainder)
        for label, size in enumerate(block_sizes):
            cnf.exactly_k(
                [block[color, label, point] for point in points],
                size,
                ("block-size", color, label),
            )

    # Resolution 1 has four size-five blocks. Every block meets A_0 by
    # alpha(G_0)<=4 and meets A_2,A_3,A_4 by the four-block capacity argument.
    # Its group sizes (4,5,5,6) force doubled groups A_2,A_3,A_4,A_4.
    # Block relabeling and independent point permutations inside each group
    # therefore put the complete resolution into this canonical pattern.
    canonical_resolution_one = {
        0: (groups[2][0], groups[2][1], groups[3][2], groups[4][4], groups[0][0]),
        1: (groups[2][2], groups[3][0], groups[3][1], groups[4][5], groups[0][1]),
        2: (groups[2][3], groups[3][3], groups[4][0], groups[4][1], groups[0][2]),
        3: (groups[2][4], groups[3][4], groups[4][2], groups[4][3], groups[0][3]),
    }
    fixed_memberships = 0
    for label, members in canonical_resolution_one.items():
        for point in members:
            cnf.add(block[1, label, point])
            fixed_memberships += 1
    if fixed_memberships != 20:
        raise AssertionError("canonical resolution must fix exactly 20 points")

    if require_forced_compositions:
        # Every size-five tight block meets A_0 by alpha(G_0)<=4 and every
        # other available group by the cross-resolution four-block capacity
        # bound. Resolutions 2 and 3 therefore have forced doubled groups.
        composition = {
            2: ((1, 3, 4, 4), (0, 1, 3, 4)),
            3: ((1, 2, 4, 4), (0, 1, 2, 4)),
        }
        for color, (doubled_groups, available_groups) in composition.items():
            for label, doubled_group in enumerate(doubled_groups):
                for point_group in available_groups:
                    cnf.exactly_k(
                        [
                            block[color, label, point]
                            for point in groups[point_group]
                        ],
                        2 if point_group == doubled_group else 1,
                        (
                            "forced-block-group-size",
                            color,
                            label,
                            point_group,
                        ),
                    )

        if fix_resolution_two_group_one:
            # Resolution 1 excludes A_1, so all five labels inside A_1 remain
            # freely permutable after its canonical pattern is fixed.  The
            # forced resolution-2 composition can therefore be named fully.
            group_one_pattern = {
                0: (groups[1][0], groups[1][1]),
                1: (groups[1][2],),
                2: (groups[1][3],),
                3: (groups[1][4],),
            }
            for label, members in group_one_pattern.items():
                for point in members:
                    cnf.add(block[2, label, point])

        # Resolution 4 has three size-five blocks and one size-four block.  An
        # unbranched instance requires only the positive intersections.  A
        # branch fixes one of all 13 possible doubled-group count vectors.
        equal_label_pairs: list[tuple[int, int, int]] = [
            (2, 2, 3),
            (3, 2, 3),
        ]
        if resolution_four_profile is None:
            for label in range(3):
                for point_group in range(4):
                    cnf.add(
                        *[
                            block[4, label, point]
                            for point in groups[point_group]
                        ]
                    )
            equal_label_pairs.extend(((4, 0, 1), (4, 1, 2)))
        else:
            doubled_groups = tuple(
                point_group
                for point_group, count in enumerate(resolution_four_profile)
                for _ in range(count)
            )
            remaining_sizes = tuple(
                len(groups[point_group]) - 3 - resolution_four_profile[point_group]
                for point_group in range(4)
            )
            if len(doubled_groups) != 3 or sum(remaining_sizes) != 4:
                raise AssertionError("invalid resolution-four branch arithmetic")
            for label, doubled_group in enumerate(doubled_groups):
                for point_group in range(4):
                    cnf.exactly_k(
                        [
                            block[4, label, point]
                            for point in groups[point_group]
                        ],
                        2 if point_group == doubled_group else 1,
                        (
                            "resolution-four-branch-size",
                            label,
                            point_group,
                        ),
                    )
            for point_group, size in enumerate(remaining_sizes):
                cnf.exactly_k(
                    [block[4, 3, point] for point in groups[point_group]],
                    size,
                    ("resolution-four-branch-size", 3, point_group),
                )
            for first_label, second_label in zip(range(2), range(1, 3)):
                if doubled_groups[first_label] == doubled_groups[second_label]:
                    equal_label_pairs.append((4, first_label, second_label))

        # Blocks with identical forced roles remain interchangeable. Order
        # each such label class by its least point.
        for color, first_label, second_label in equal_label_pairs:
            for point in points:
                cnf.add(
                    -block[color, second_label, point],
                    *[
                        block[color, first_label, earlier]
                        for earlier in range(point)
                    ],
                )

    for first_color, second_color in itertools.combinations(tight_colors, 2):
        for first_label in range(4):
            for second_label in range(4):
                for left, right in itertools.combinations(points, 2):
                    cnf.add(
                        -block[first_color, first_label, left],
                        -block[first_color, first_label, right],
                        -block[second_color, second_label, left],
                        -block[second_color, second_label, right],
                    )

    cnf.exactly_k(
        list(exceptional.values()),
        exceptional_edge_count,
        ("exceptional-edge-count",),
    )
    five_sets = 0
    for subset in itertools.combinations(graph_points, 5):
        cnf.add(
            *[
                exceptional[left, right]
                for left, right in itertools.combinations(subset, 2)
            ]
        )
        five_sets += 1
    six_sets = 0
    for subset in itertools.combinations(graph_points, 6):
        cnf.add(
            *[
                -exceptional[left, right]
                for left, right in itertools.combinations(subset, 2)
            ]
        )
        six_sets += 1

    for (left, right), edge in exceptional.items():
        for color in tight_colors:
            for label in range(4):
                cnf.add(
                    -edge,
                    -block[color, label, left],
                    -block[color, label, right],
                )

    private_witness_selectors = 0
    if require_edge_minimality:
        for (left, right), edge in exceptional.items():
            remaining = [
                point for point in graph_points if point not in (left, right)
            ]
            selectors = [
                cnf.variable("private-witness-vertex", left, right, point)
                for point in remaining
            ]
            private_witness_selectors += len(selectors)

            first_gated_clause = len(cnf.clauses)
            cnf.exactly_k(
                selectors,
                3,
                ("private-witness-size", left, right),
            )
            for clause in cnf.clauses[first_gated_clause:]:
                clause.append(-edge)
            for point, selector in zip(remaining, selectors, strict=True):
                cnf.add(-selector, edge)
                cnf.add(
                    -selector,
                    -exceptional[tuple(sorted((left, point)))],
                )
                cnf.add(
                    -selector,
                    -exceptional[tuple(sorted((right, point)))],
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
                    -exceptional[pair],
                )

    return cnf, {
        "case": f"unbalanced{exceptional_edge_count}",
        "groups": groups,
        "graph_points": graph_points,
        "exceptional_variables": len(exceptional),
        "exceptional_edge_count": exceptional_edge_count,
        "five_sets": five_sets,
        "six_sets": six_sets,
        "fixed_resolution_memberships": fixed_memberships,
        "private_witness_selectors": private_witness_selectors,
        "forced_compositions": require_forced_compositions,
        "resolution_four_profile": resolution_four_profile,
        "fixed_resolution_two_group_one": fix_resolution_two_group_one,
    }


def build_instance(
    case: str,
    require_edge_minimality: bool = False,
    require_forced_compositions: bool = False,
    resolution_four_profile: tuple[int, int, int, int] | None = None,
    fix_resolution_two_group_one: bool = False,
) -> tuple[CNF, dict[str, object]]:
    if case == "balanced46":
        if (
            require_forced_compositions
            or resolution_four_profile is not None
            or fix_resolution_two_group_one
        ):
            raise ValueError("balanced46 already encodes every forced composition")
        cnf, metadata = build_balanced_base(
            require_edge_minimality=require_edge_minimality,
            exceptional_edge_count=46,
        )
        metadata = dict(metadata)
        metadata["case"] = case
        return cnf, metadata
    if case == "unbalanced50":
        return build_unbalanced(
            require_edge_minimality,
            require_forced_compositions,
            resolution_four_profile,
            fix_resolution_two_group_one,
        )
    raise ValueError(f"unsupported local-206 near case {case!r}")


def render(
    case: str,
    require_edge_minimality: bool = False,
    require_forced_compositions: bool = False,
    resolution_four_profile: tuple[int, int, int, int] | None = None,
    fix_resolution_two_group_one: bool = False,
) -> str:
    cnf, metadata = build_instance(
        case,
        require_edge_minimality,
        require_forced_compositions,
        resolution_four_profile,
        fix_resolution_two_group_one,
    )
    order = 20 if case == "balanced46" else 21
    lines = [
        f"c ERDOS617 local L=206 classification-free compatibility, version 1",
        (
            f"c case={case} exceptional_order={order} "
            f"exceptional_edges={metadata['exceptional_edge_count']} "
            "alpha<=4 omega<=5"
        ),
        (
            f"c exceptional_variables={metadata['exceptional_variables']} "
            f"five_sets={metadata['five_sets']} six_sets={metadata['six_sets']} "
            f"fixed_resolution_memberships="
            f"{metadata['fixed_resolution_memberships']} "
            f"private_witness_selectors="
            f"{metadata['private_witness_selectors']} "
            f"forced_compositions="
            f"{int(bool(metadata.get('forced_compositions', False)))} "
            "resolution_four_profile="
            + (
                "none"
                if metadata.get("resolution_four_profile") is None
                else ",".join(
                    map(str, metadata["resolution_four_profile"])
                )
            )
            + " fixed_resolution_two_group_one="
            + str(int(bool(metadata.get("fixed_resolution_two_group_one", False))))
        ),
        f"p cnf {cnf.variables} {len(cnf.clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in cnf.clauses)
    return "\n".join(lines) + "\n"


def parse_resolution_four_profile(text: str) -> tuple[int, int, int, int]:
    fields = tuple(map(int, text.split(",")))
    if len(fields) != 4 or fields not in resolution_four_profiles():
        raise argparse.ArgumentTypeError("expected one valid four-entry profile")
    return fields


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--case",
        choices=("balanced46", "unbalanced50"),
        required=True,
    )
    parser.add_argument("--fix-resolution-two-group-one", action="store_true")
    parser.add_argument("--minimal", action="store_true")
    parser.add_argument("--forced-compositions", action="store_true")
    parser.add_argument(
        "--resolution-four-profile",
        type=parse_resolution_four_profile,
    )
    args = parser.parse_args()
    args.output.write_text(
        render(
            args.case,
            args.minimal,
            args.forced_compositions,
            args.resolution_four_profile,
            args.fix_resolution_two_group_one,
        ),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

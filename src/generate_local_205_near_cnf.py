#!/usr/bin/env python3
"""Generate a necessary CNF for the balanced local-count-205 branch."""

from __future__ import annotations

import argparse
import itertools
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_204_cnf import CNF  # noqa: E402


def build_instance(
    require_edge_minimality: bool = False,
    exceptional_edge_count: int = 45,
    fix_resolution_two_group_one: bool = False,
) -> tuple[CNF, dict[str, object]]:
    cnf = CNF()
    points = tuple(range(25))
    tight_colors = (1, 2, 3, 4)
    # Because the exceptional graph is variable, every point of B_0 can be
    # relabeled. Canonically fix all five spoke groups before encoding blocks.
    groups = {
        0: tuple(range(20, 25)),
        1: tuple(range(0, 5)),
        2: tuple(range(5, 10)),
        3: tuple(range(10, 15)),
        4: tuple(range(15, 20)),
    }
    graph_points = tuple(point for color in tight_colors for point in groups[color])

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
        for label in range(4):
            cnf.exactly_k(
                [block[color, label, point] for point in points],
                5,
                ("block-size", color, label),
            )

    # Every tight block meets all four available spoke groups and therefore has
    # composition (2,1,1,1); its doubled group canonically labels the block.
    for color in tight_colors:
        available_groups = [0] + [other for other in tight_colors if other != color]
        for label, doubled_group in enumerate(available_groups):
            for point_group in available_groups:
                cnf.exactly_k(
                    [
                        block[color, label, point]
                        for point in groups[point_group]
                    ],
                    2 if point_group == doubled_group else 1,
                    ("block-group-size", color, label, point_group),
                )

    # Independently permute the five labels inside each spoke group to fix all
    # of resolution 1. This is a complete orbit representative, not a search
    # restriction; the exceptional graph variables are permuted simultaneously.
    resolution_one_groups = [0, 2, 3, 4]
    for point_group in resolution_one_groups:
        doubled_label = resolution_one_groups.index(point_group)
        group_points = groups[point_group]
        cnf.add(block[1, doubled_label, group_points[0]])
        cnf.add(block[1, doubled_label, group_points[1]])
        other_labels = [label for label in range(4) if label != doubled_label]
        for point, label in zip(group_points[2:], other_labels, strict=True):
            cnf.add(block[1, label, point])

    if fix_resolution_two_group_one:
        # Resolution 1 excludes A_1, so its five point labels remain freely
        # permutable after the complete resolution-1 orbit fix.  Resolution 2
        # has A_1 multiplicities (1,2,1,1) in its canonically doubled-group
        # labeled blocks.  Name the doubled pair first and the singletons in
        # increasing block-label order.  Exceptional-edge variables are
        # relabeled with their endpoints, so this is a complete point-symmetry
        # quotient rather than a restriction on the graph family.
        group_one = groups[1]
        canonical_group_one = {
            1: (group_one[0], group_one[1]),
            0: (group_one[2],),
            2: (group_one[3],),
            3: (group_one[4],),
        }
        for label, members in canonical_group_one.items():
            for point in members:
                cnf.add(block[2, label, point])

    # Blocks of two colors share at most one point.
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

    # The exceptional color graph has complement size 145, hits every five-set,
    # and cannot itself contain a monochromatic K6.
    cnf.exactly_k(
        list(exceptional.values()),
        exceptional_edge_count,
        ("exceptional-edge-count",),
    )
    for subset in itertools.combinations(graph_points, 5):
        cnf.add(
            *[
                exceptional[tuple(sorted((left, right)))]
                for left, right in itertools.combinations(subset, 2)
            ]
        )
    for subset in itertools.combinations(graph_points, 6):
        cnf.add(
            *[
                -exceptional[tuple(sorted((left, right)))]
                for left, right in itertools.combinations(subset, 2)
            ]
        )

    # A pair cannot simultaneously be exceptional and lie in a tight clique.
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
        # If the exact one-edge-smaller necessary system has already been
        # excluded, deleting any exceptional edge must create an independent
        # five-set. Such a set has that edge as its unique exceptional edge.
        # For each potential edge, select its three other vertices directly.
        for (left, right), edge in exceptional.items():
            remaining = [
                point for point in graph_points if point not in (left, right)
            ]
            selectors = [
                cnf.variable("private-witness-vertex", left, right, point)
                for point in remaining
            ]
            private_witness_selectors += len(selectors)

            # Gate a standard exactly-three encoding by the exceptional edge.
            # If the edge is absent, all selectors are false and the relaxed
            # counter clauses impose no condition.  If it is present, exactly
            # three vertices are selected.
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

    metadata: dict[str, object] = {
        "exceptional_variables": len(exceptional),
        "exceptional_edge_count": exceptional_edge_count,
        "five_sets": 15_504,
        "six_sets": 38_760,
        "fixed_resolution_memberships": 20,
        "private_witness_selectors": private_witness_selectors,
    }
    if fix_resolution_two_group_one:
        metadata["fixed_resolution_two_group_one"] = True
    return cnf, metadata


def render(require_edge_minimality: bool = False) -> str:
    cnf, metadata = build_instance(require_edge_minimality)
    metadata_line = (
        f"c exceptional_variables={metadata['exceptional_variables']} "
        f"five_sets={metadata['five_sets']} six_sets={metadata['six_sets']} "
        f"fixed_resolution_memberships={metadata['fixed_resolution_memberships']}"
    )
    if require_edge_minimality:
        metadata_line += (
            f" private_witness_selectors={metadata['private_witness_selectors']}"
        )
    lines = [
        (
            "c ERDOS617 balanced local L=205 near-extremal compatibility, "
            f"version {'4-compact-minimal' if require_edge_minimality else '2'}"
        ),
        "c exceptional graph variable: 20 vertices, 45 edges, alpha<=4, omega<=5",
        metadata_line,
        f"p cnf {cnf.variables} {len(cnf.clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in cnf.clauses)
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--minimal", action="store_true")
    args = parser.parse_args()
    args.output.write_text(
        render(require_edge_minimality=args.minimal),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

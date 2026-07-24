#!/usr/bin/env python3
"""Generate exact fixed-center colorings with local count 210.

The center is implicit.  Its 25 incident edges have the fixed spoke colors
given by one canonical degree profile.  Every edge among the 25 neighbors is
assigned exactly one of five colors.  The formula enforces all six-set color
requirements, including the sets containing the center, and requires the
center's exact local count to be 210.

Unlike the E015 projection with ``availability-unforced-edge`` variables, a
satisfying assignment of this formula is a complete balanced coloring of
K_26 (with the implicit center added).  Conversely, any balanced coloring
having a vertex of local count 210 can be relabeled into one of the fourteen
canonical profile formulas.
"""

from __future__ import annotations

import argparse
import itertools
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_204_cnf import CNF  # noqa: E402
from src.generate_local_210_exact_cnf import (  # noqa: E402
    COLORS,
    LOCAL_COUNT,
    POINTS,
    PROFILES,
    groups_for_profile,
)

NEIGHBOR_SIX_SET_CLAUSES = 5 * 177_100


def build_instance(profile: str):
    groups = groups_for_profile(profile)
    point_group = {
        point: color for color, group in groups.items() for point in group
    }
    graph_points = {
        color: tuple(point for point in POINTS if point not in groups[color])
        for color in COLORS
    }

    cnf = CNF()
    edge = {
        (color, left, right): cnf.variable("edge-color", color, left, right)
        for color in COLORS
        for left, right in itertools.combinations(POINTS, 2)
    }

    edge_one_hot_clauses = 0
    for left, right in itertools.combinations(POINTS, 2):
        colors = [edge[color, left, right] for color in COLORS]
        cnf.exactly_one(colors)
        edge_one_hot_clauses += 1 + len(tuple(itertools.combinations(colors, 2)))

    local_edges = [
        edge[color, left, right]
        for color in COLORS
        for left, right in itertools.combinations(graph_points[color], 2)
    ]
    cnf.exactly_k(local_edges, LOCAL_COUNT, ("exact-local-count", profile))

    center_coverage_clauses = 0
    for color in COLORS:
        for subset in itertools.combinations(graph_points[color], 5):
            cnf.add(
                *[
                    edge[color, left, right]
                    for left, right in itertools.combinations(subset, 2)
                ]
            )
            center_coverage_clauses += 1

    return cnf, {
        "profile": profile,
        "degree_profile": PROFILES[profile],
        "groups": groups,
        "point_group": point_group,
        "graph_points": graph_points,
        "edge": edge,
        "local_edges": tuple(local_edges),
        "edge_one_hot_clauses": edge_one_hot_clauses,
        "center_coverage_clauses": center_coverage_clauses,
    }


def neighbor_coverage_clauses(metadata):
    edge = metadata["edge"]
    observed = 0
    for subset in itertools.combinations(POINTS, 6):
        pairs = tuple(itertools.combinations(subset, 2))
        for color in COLORS:
            observed += 1
            yield [edge[color, left, right] for left, right in pairs]
    if observed != NEIGHBOR_SIX_SET_CLAUSES:
        raise AssertionError("fixed-center neighbor coverage is incomplete")


def render(profile: str, output: Path) -> tuple[int, int]:
    cnf, metadata = build_instance(profile)
    clause_count = len(cnf.clauses) + NEIGHBOR_SIX_SET_CLAUSES
    with output.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 E015 exact fixed-center coloring, version 1\n")
        stream.write(
            f"c profile={profile} degrees="
            + ",".join(map(str, metadata["degree_profile"]))
            + " exact_coloring=1\n"
        )
        stream.write(
            f"c local_count={LOCAL_COUNT} "
            f"neighbor_six_set_color_clauses={NEIGHBOR_SIX_SET_CLAUSES}\n"
        )
        stream.write(f"p cnf {cnf.variables} {clause_count}\n")
        observed = 0
        for clause in itertools.chain(
            cnf.clauses, neighbor_coverage_clauses(metadata)
        ):
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    return cnf.variables, clause_count


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--profile", choices=tuple(PROFILES), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.profile, args.output)
    print(
        "LOCAL-210-COLORING-CNF-PASS "
        f"profile={args.profile} variables={variables} clauses={clauses}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

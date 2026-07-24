#!/usr/bin/env python3
"""Generate classification-free exact-local-count-210 necessary CNFs.

For each canonical spoke-degree profile, an edge variable records every
color-c edge whose two endpoints lie in B_c.  The formula enforces the exact
local count, all center-containing six-set consequences, pairwise edge-color
disjointness, and the E014 neighbor-color availability condition.

Edges incident to a color's spoke group are deliberately not assigned exact
colors.  The unforced variables only state that such an edge may use one of
its endpoint spoke colors.  Therefore this is a necessary relaxation of an
unrestricted balanced K26 coloring, not a sufficient coloring model.
"""

from __future__ import annotations

import argparse
import itertools
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_204_cnf import CNF  # noqa: E402

POINTS = tuple(range(25))
COLORS = tuple(range(5))
LOCAL_COUNT = 210
SIX_SET_CLAUSES = 5 * 177_100

PROFILE_TUPLES = (
    (1, 5, 5, 5, 9),
    (1, 5, 5, 6, 8),
    (1, 5, 5, 7, 7),
    (1, 5, 6, 6, 7),
    (1, 6, 6, 6, 6),
    (2, 5, 5, 5, 8),
    (2, 5, 5, 6, 7),
    (2, 5, 6, 6, 6),
    (3, 5, 5, 5, 7),
    (3, 5, 5, 6, 6),
    (4, 4, 5, 5, 7),
    (4, 4, 5, 6, 6),
    (4, 5, 5, 5, 6),
    (5, 5, 5, 5, 5),
)
PROFILES = {"p" + "".join(map(str, profile)): profile for profile in PROFILE_TUPLES}


def groups_for_profile(profile: str) -> dict[int, tuple[int, ...]]:
    if profile not in PROFILES:
        raise ValueError(f"unknown local-count-210 profile {profile!r}")
    groups: dict[int, tuple[int, ...]] = {}
    cursor = 0
    for color, size in enumerate(PROFILES[profile]):
        groups[color] = tuple(range(cursor, cursor + size))
        cursor += size
    if cursor != 25:
        raise AssertionError("spoke groups do not partition the 25 neighbors")
    return groups


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
        (color, left, right): cnf.variable("local-edge", color, left, right)
        for color in COLORS
        for left, right in itertools.combinations(graph_points[color], 2)
    }
    ordered_edges = [
        edge[color, left, right]
        for color in COLORS
        for left, right in itertools.combinations(graph_points[color], 2)
    ]
    cnf.exactly_k(ordered_edges, LOCAL_COUNT, ("exact-local-count", profile))

    five_set_clauses = 0
    six_set_nonclique_clauses = 0
    for color in COLORS:
        for subset in itertools.combinations(graph_points[color], 5):
            cnf.add(
                *[
                    edge[color, left, right]
                    for left, right in itertools.combinations(subset, 2)
                ]
            )
            five_set_clauses += 1
        for subset in itertools.combinations(graph_points[color], 6):
            cnf.add(
                *[
                    -edge[color, left, right]
                    for left, right in itertools.combinations(subset, 2)
                ]
            )
            six_set_nonclique_clauses += 1

    pair_disjointness_clauses = 0
    structural_by_pair: dict[tuple[int, int], tuple[int, ...]] = {}
    for left, right in itertools.combinations(POINTS, 2):
        structural = tuple(
            edge[color, left, right]
            for color in COLORS
            if color not in (point_group[left], point_group[right])
        )
        if len(structural) not in (3, 4):
            raise AssertionError("neighbor pair has wrong structural-color count")
        structural_by_pair[left, right] = structural
        for first, second in itertools.combinations(structural, 2):
            cnf.add(-first, -second)
            pair_disjointness_clauses += 1

    unforced: dict[tuple[int, int], int] = {}
    unforced_definition_clauses = 0
    for left, right in itertools.combinations(POINTS, 2):
        structural = structural_by_pair[left, right]
        free = cnf.variable("availability-unforced-edge", left, right)
        unforced[left, right] = free
        for present in structural:
            cnf.add(-free, -present)
            unforced_definition_clauses += 1
        cnf.add(*structural, free)
        unforced_definition_clauses += 1

    return cnf, {
        "profile": profile,
        "degree_profile": PROFILES[profile],
        "groups": groups,
        "point_group": point_group,
        "graph_points": graph_points,
        "edge": edge,
        "ordered_edges": tuple(ordered_edges),
        "unforced": unforced,
        "five_set_clauses": five_set_clauses,
        "six_set_nonclique_clauses": six_set_nonclique_clauses,
        "pair_disjointness_clauses": pair_disjointness_clauses,
        "unforced_definition_clauses": unforced_definition_clauses,
    }


def coverage_clauses(metadata):
    point_group = metadata["point_group"]
    edge = metadata["edge"]
    unforced = metadata["unforced"]
    observed = 0
    for subset in itertools.combinations(POINTS, 6):
        pairs = tuple(itertools.combinations(subset, 2))
        for color in COLORS:
            clause = [
                (
                    unforced[left, right]
                    if color in (point_group[left], point_group[right])
                    else edge[color, left, right]
                )
                for left, right in pairs
            ]
            observed += 1
            yield clause
    if observed != SIX_SET_CLAUSES:
        raise AssertionError("local-count-210 neighbor coverage is incomplete")


def render(profile: str, output: Path) -> tuple[int, int]:
    cnf, metadata = build_instance(profile)
    clause_count = len(cnf.clauses) + SIX_SET_CLAUSES
    with output.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 E015 exact-local-count-210 projection, version 1\n")
        stream.write(
            f"c profile={profile} degrees="
            + ",".join(map(str, metadata["degree_profile"]))
            + " necessary_relaxation=1\n"
        )
        stream.write(
            f"c local_count={LOCAL_COUNT} "
            f"neighbor_six_set_color_clauses={SIX_SET_CLAUSES}\n"
        )
        stream.write(f"p cnf {cnf.variables} {clause_count}\n")
        observed = 0
        for clause in itertools.chain(cnf.clauses, coverage_clauses(metadata)):
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
        "LOCAL-210-EXACT-CNF-PASS "
        f"profile={args.profile} variables={variables} clauses={clauses}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

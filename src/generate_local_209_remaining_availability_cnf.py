#!/usr/bin/env python3
"""Neighbor-six-set color availability for the remaining E014 targets."""

from __future__ import annotations

import argparse
import itertools
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_209_double_classified_u50_full_canonical_cnf import (  # noqa: E402
    build_instance as build_u50,
)
from src.generate_local_209_near_cnf import build_instance as build_near  # noqa: E402

POINTS = tuple(range(25))
COLORS = tuple(range(5))
SIX_SET_CLAUSES = 5 * 177_100


def descend_local(metadata: dict[str, object]) -> dict[str, object]:
    current = metadata
    while "groups" not in current:
        nested = current.get("base_metadata")
        if not isinstance(nested, dict):
            raise AssertionError("availability metadata has no local group layer")
        current = nested
    return current


FAMILIES = {
    "u50_a1": {
        "builder": lambda: build_u50("u4455_a1"),
        "exceptional_colors": (0, 4),
        "tight_colors": (1, 2, 3),
        "colored_exceptional_names": True,
    },
    "u50_a2": {
        "builder": lambda: build_u50("u4455_a2"),
        "exceptional_colors": (0, 4),
        "tight_colors": (1, 2, 3),
        "colored_exceptional_names": True,
    },
    "unbalanced53": {
        "builder": lambda: build_near("unbalanced53", True, True, None, True),
        "exceptional_colors": (0,),
        "tight_colors": (1, 2, 3, 4),
        "colored_exceptional_names": False,
    },
}


def build_instance(family: str):
    if family not in FAMILIES:
        raise ValueError(f"unknown E014 availability family {family!r}")
    config = FAMILIES[family]
    cnf, base_metadata = config["builder"]()
    local = descend_local(base_metadata)
    groups = {int(color): tuple(points) for color, points in local["groups"].items()}
    if set(groups) != set(COLORS) or sorted(
        itertools.chain.from_iterable(groups.values())
    ) != list(POINTS):
        raise AssertionError(f"{family}: spoke groups do not partition points")
    point_group = {
        point: color for color, points in groups.items() for point in points
    }
    exceptional_colors = tuple(config["exceptional_colors"])
    tight_colors = tuple(config["tight_colors"])
    if set(exceptional_colors) | set(tight_colors) != set(COLORS):
        raise AssertionError(f"{family}: color types do not cover all colors")

    counted: dict[tuple[int, int, int], int] = {}
    added_tight_variables = 0
    added_tight_definition_clauses = 0
    for color in COLORS:
        graph_points = tuple(point for point in POINTS if point_group[point] != color)
        for left, right in itertools.combinations(graph_points, 2):
            if color in exceptional_colors:
                name = (
                    ("exceptional-edge", color, left, right)
                    if config["colored_exceptional_names"]
                    else ("exceptional-edge", left, right)
                )
                counted[color, left, right] = cnf.names[name]
                continue
            edge = cnf.variable("availability-counted-edge", color, left, right)
            counted[color, left, right] = edge
            added_tight_variables += 1
            for label in range(4):
                left_block = cnf.names[("block", color, label, left)]
                right_block = cnf.names[("block", color, label, right)]
                cnf.add(-left_block, -right_block, edge)
                cnf.add(-edge, -left_block, right_block)
                added_tight_definition_clauses += 2

    unforced: dict[tuple[int, int], int] = {}
    added_unforced_definition_clauses = 0
    for left, right in itertools.combinations(POINTS, 2):
        structural = [
            counted[color, left, right]
            for color in COLORS
            if color not in (point_group[left], point_group[right])
        ]
        if len(structural) not in (3, 4):
            raise AssertionError(f"{family}: wrong pair structural-color count")
        free = cnf.variable("availability-unforced-edge", left, right)
        unforced[left, right] = free
        for edge in structural:
            cnf.add(-free, -edge)
            added_unforced_definition_clauses += 1
        cnf.add(*structural, free)
        added_unforced_definition_clauses += 1

    expected_tight = sum(
        len(tuple(itertools.combinations(
            (point for point in POINTS if point_group[point] != color), 2
        )))
        for color in tight_colors
    )
    if added_tight_variables != expected_tight or len(unforced) != 300:
        raise AssertionError(f"{family}: availability auxiliary count changed")
    return cnf, {
        "family": family,
        "groups": groups,
        "point_group": point_group,
        "exceptional_colors": exceptional_colors,
        "tight_colors": tight_colors,
        "counted": counted,
        "unforced": unforced,
        "base_metadata": base_metadata,
        "added_tight_variables": added_tight_variables,
        "added_unforced_variables": len(unforced),
        "added_definition_clauses": (
            added_tight_definition_clauses + added_unforced_definition_clauses
        ),
    }


def coverage_clauses(metadata):
    point_group = metadata["point_group"]
    counted = metadata["counted"]
    unforced = metadata["unforced"]
    observed = 0
    for subset in itertools.combinations(POINTS, 6):
        for color in COLORS:
            clause = [
                (
                    unforced[left, right]
                    if color in (point_group[left], point_group[right])
                    else counted[color, left, right]
                )
                for left, right in itertools.combinations(subset, 2)
            ]
            observed += 1
            yield clause
    if observed != SIX_SET_CLAUSES:
        raise AssertionError("remaining availability six-set count changed")


def render(family: str, output: Path) -> tuple[int, int]:
    cnf, metadata = build_instance(family)
    clause_count = len(cnf.clauses) + SIX_SET_CLAUSES
    with output.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(
            "c ERDOS617 E014 remaining-target neighbor-color availability, version 1\n"
        )
        stream.write(f"c family={family} necessary_relaxation=1\n")
        stream.write(
            f"c definitions={metadata['added_definition_clauses']} "
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
    parser.add_argument("--family", choices=tuple(FAMILIES), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.family, args.output)
    print(
        "LOCAL-209-REMAINING-AVAILABILITY-CNF-PASS "
        f"family={args.family} variables={variables} clauses={clauses} "
        f"neighbor_six_set_color_clauses={SIX_SET_CLAUSES}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

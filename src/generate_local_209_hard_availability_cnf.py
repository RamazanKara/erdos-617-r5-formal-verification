#!/usr/bin/env python3
"""Add neighbor-six-set color-availability constraints to E014 hard45_44.

For a neighbor pair and a color whose spoke group contains neither endpoint,
the local incidence structure says exactly whether that pair has the color.
If neither endpoint's spoke color is structurally overridden in this way, the
pair is free to take one of its endpoint spoke colors.  Every neighbor six-set
in an actual balanced K26 coloring must therefore have, for every color,
either a counted edge of that color or an unforced edge incident to its spoke
group.  The clauses here encode precisely that necessary condition.

This is still a relaxation: it does not choose one globally consistent color
for every unforced pair.  SAT would not be a K26 coloring; UNSAT, once fully
certified, would exclude the named local branch.
"""

from __future__ import annotations

import argparse
import itertools
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_209_double_classified_hard_cnf import (  # noqa: E402
    build_instance as build_base,
)

POINTS = tuple(range(25))
COLORS = tuple(range(5))
EXCEPTIONAL_COLORS = (0, 1)
TIGHT_COLORS = (2, 3, 4)
COUNTER_6080 = 6080
COUNTER_4830 = 4830
SIX_SET_CLAUSES = 5 * 177_100
SCOPES = {
    "child": (-COUNTER_6080, COUNTER_4830),
    "base": (),
}


def build_instance():
    cnf, metadata = build_base()
    local = metadata["base_metadata"]["base_metadata"]
    groups = {int(color): tuple(points) for color, points in local["groups"].items()}
    if set(groups) != set(COLORS) or sorted(
        itertools.chain.from_iterable(groups.values())
    ) != list(POINTS):
        raise AssertionError("hard availability groups do not partition points")
    point_group = {
        point: color for color, points in groups.items() for point in points
    }

    counted: dict[tuple[int, int, int], int] = {}
    added_tight_variables = 0
    added_tight_definition_clauses = 0
    for color in COLORS:
        graph_points = tuple(point for point in POINTS if point_group[point] != color)
        for left, right in itertools.combinations(graph_points, 2):
            if color in EXCEPTIONAL_COLORS:
                counted[color, left, right] = cnf.names[
                    ("exceptional-edge", color, left, right)
                ]
                continue
            edge = cnf.variable("counted-edge", color, left, right)
            counted[color, left, right] = edge
            added_tight_variables += 1
            for label in range(4):
                left_block = cnf.names[("block", color, label, left)]
                right_block = cnf.names[("block", color, label, right)]
                # Same block implies the counted edge.  Conversely, the
                # counted edge forces right to have whichever unique label
                # left has, hence the two endpoints share a block.
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
            raise AssertionError("neighbor pair has wrong structural-color count")
        free = cnf.variable("unforced-edge", left, right)
        unforced[left, right] = free
        for edge in structural:
            cnf.add(-free, -edge)
            added_unforced_definition_clauses += 1
        cnf.add(*structural, free)
        added_unforced_definition_clauses += 1

    if (
        added_tight_variables,
        len(unforced),
        added_tight_definition_clauses,
        added_unforced_definition_clauses,
    ) != (570, 300, 4560, 1250):
        raise AssertionError("hard availability definition dimensions changed")
    return cnf, {
        "groups": groups,
        "point_group": point_group,
        "counted": counted,
        "unforced": unforced,
        "base_metadata": metadata,
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
        pairs = tuple(itertools.combinations(subset, 2))
        for color in COLORS:
            clause = []
            for left, right in pairs:
                if color in (point_group[left], point_group[right]):
                    clause.append(unforced[left, right])
                else:
                    clause.append(counted[color, left, right])
            if len(clause) != 15:
                raise AssertionError("six-set availability clause has wrong length")
            observed += 1
            yield clause
    if observed != SIX_SET_CLAUSES:
        raise AssertionError("hard availability six-set count changed")


def render(output: Path, scope: str = "child") -> tuple[int, int]:
    if scope not in SCOPES:
        raise ValueError(f"unknown hard availability scope {scope!r}")
    cnf, metadata = build_instance()
    if cnf.names.get(("counter", "exceptional-edge-count", 0, 95, 23)) != COUNTER_6080:
        raise AssertionError("hard availability counter-6080 mapping changed")
    if cnf.names.get(("counter", "exceptional-edge-count", 0, 68, 15)) != COUNTER_4830:
        raise AssertionError("hard availability counter-4830 mapping changed")
    units = SCOPES[scope]
    clause_count = len(cnf.clauses) + SIX_SET_CLAUSES + len(units)
    with output.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 E014 hard45_44 neighbor-color availability, version 1\n")
        if scope == "child":
            stream.write("c necessary relaxation; exact units counter6080=0 counter4830=1\n")
        else:
            stream.write("c necessary relaxation; unsplit hard45_44 base\n")
        stream.write(
            f"c definitions={metadata['added_definition_clauses']} "
            f"neighbor_six_set_color_clauses={SIX_SET_CLAUSES}\n"
        )
        stream.write(f"p cnf {cnf.variables} {clause_count}\n")
        observed = 0
        for clause in itertools.chain(cnf.clauses, coverage_clauses(metadata)):
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for unit in units:
            stream.write(f"{unit} 0\n")
            observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    return cnf.variables, clause_count


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--scope", choices=tuple(SCOPES), default="child")
    args = parser.parse_args()
    variables, clauses = render(args.output, args.scope)
    print(
        "LOCAL-209-HARD-AVAILABILITY-CNF-PASS "
        f"scope={args.scope} variables={variables} clauses={clauses} "
        f"neighbor_six_set_color_clauses={SIX_SET_CLAUSES}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

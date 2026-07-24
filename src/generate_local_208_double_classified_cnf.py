#!/usr/bin/env python3
"""Generate exhaustive Kang--Pikhurko branches for E013 double exceptions."""

from __future__ import annotations

import argparse
import itertools
import sys
from collections import defaultdict
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_204_cnf import (  # noqa: E402
    exceptional_color_edges,
    local_205_cases,
    representative_cases,
)
from src.generate_local_208_double_cnf import (  # noqa: E402
    build_instance as build_double_base,
)


def template_catalogs():
    representative = representative_cases()
    balanced = {
        case_id: (parts, source, target, subset_size)
        for case_id, case, parts, source, target, subset_size in representative
        if case == "balanced" and max(parts) <= 5
    }
    order_19 = {
        case_id: (parts, source, target, subset_size)
        for case_id, case, parts, source, target, subset_size in representative
        if case == "unbalanced"
    }
    order_21 = {
        case_id: (parts, source, target, subset_size)
        for case_id, _, parts, source, target, subset_size in local_205_cases()
        if max(parts) <= 5
    }
    if (len(balanced), len(order_21), len(order_19)) != (4, 2, 2):
        raise AssertionError("wrong double-exception template catalogs")
    return balanced, order_21, order_19


def branch_catalog() -> list[tuple[str, str, str]]:
    balanced, order_21, order_19 = template_catalogs()
    branches = [
        ("balanced_double44", first, second)
        for first_index, first in enumerate(balanced)
        for second in tuple(balanced)[first_index:]
    ]
    branches.extend(
        ("unbalanced_double49_39", first, second)
        for first in order_21
        for second in order_19
    )
    if len(branches) != 14:
        raise AssertionError("wrong classified double-exception branch count")
    return branches


def true_twin_quotient(
    order: int, edges: set[tuple[int, int]]
) -> tuple[tuple[tuple[int, ...], ...], tuple[tuple[bool, ...], ...]]:
    closed = [{vertex} for vertex in range(order)]
    for left, right in edges:
        closed[left].add(right)
        closed[right].add(left)
    grouped: dict[frozenset[int], list[int]] = defaultdict(list)
    for vertex, neighborhood in enumerate(closed):
        grouped[frozenset(neighborhood)].append(vertex)
    classes = tuple(
        tuple(vertices)
        for vertices in sorted(grouped.values(), key=lambda vertices: vertices[0])
    )
    edge_set = {tuple(sorted(pair)) for pair in edges}
    adjacency: list[list[bool]] = []
    for first_index, first_class in enumerate(classes):
        row = []
        for second_index, second_class in enumerate(classes):
            observed = {
                tuple(sorted((left, right))) in edge_set
                for left in first_class
                for right in second_class
                if left != right
            }
            if not observed:
                # Two vertices can never occupy the same singleton class.
                value = False
            elif len(observed) == 1:
                value = observed.pop()
            else:
                raise AssertionError(
                    f"nonuniform twin quotient classes {first_index},{second_index}"
                )
            row.append(value)
        adjacency.append(row)
    if len(classes) != 7:
        raise AssertionError("Kang--Pikhurko template must have seven twin classes")
    return classes, tuple(tuple(row) for row in adjacency)


def add_template_isomorphism(
    cnf,
    color: int,
    graph_points: tuple[int, ...],
    template_id: str,
    parameters: tuple[tuple[int, int, int, int], int, int, int],
) -> dict[str, object]:
    parts, source, target, subset_size = parameters
    template_edges = exceptional_color_edges(
        parts, source, target, subset_size
    )
    if len(graph_points) != sum(parts) + 1:
        raise AssertionError("template order does not match exceptional domain")
    classes, adjacency = true_twin_quotient(len(graph_points), template_edges)
    membership = {
        (point, class_index): cnf.variable(
            "exceptional-template-class",
            color,
            template_id,
            class_index,
            point,
        )
        for point in graph_points
        for class_index in range(len(classes))
    }
    for point in graph_points:
        cnf.exactly_one(
            [membership[point, class_index] for class_index in range(len(classes))]
        )
    for class_index, vertices in enumerate(classes):
        cnf.exactly_k(
            [membership[point, class_index] for point in graph_points],
            len(vertices),
            ("exceptional-template-class-size", color, template_id, class_index),
        )

    adjacency_clauses = 0
    for left, right in itertools.combinations(graph_points, 2):
        edge = cnf.names[("exceptional-edge", color, left, right)]
        for first_class in range(len(classes)):
            for second_class in range(len(classes)):
                cnf.add(
                    -membership[left, first_class],
                    -membership[right, second_class],
                    edge if adjacency[first_class][second_class] else -edge,
                )
                adjacency_clauses += 1
    return {
        "template_id": template_id,
        "parts": parts,
        "source": source,
        "target": target,
        "subset_size": subset_size,
        "template_edges": len(template_edges),
        "class_sizes": tuple(map(len, classes)),
        "class_adjacency": adjacency,
        "membership_variables": len(membership),
        "adjacency_clauses": adjacency_clauses,
    }


def build_instance(case: str, first_template: str, second_template: str):
    balanced, order_21, order_19 = template_catalogs()
    if case == "balanced_double44":
        if first_template not in balanced or second_template not in balanced:
            raise ValueError("unknown balanced classified template")
        if tuple(balanced).index(first_template) > tuple(balanced).index(second_template):
            raise ValueError("balanced template pair must be in canonical order")
        template_by_color = {
            0: (first_template, balanced[first_template]),
            1: (second_template, balanced[second_template]),
        }
    elif case == "unbalanced_double49_39":
        if first_template not in order_21 or second_template not in order_19:
            raise ValueError("unknown unbalanced classified template")
        template_by_color = {
            0: (first_template, order_21[first_template]),
            4: (second_template, order_19[second_template]),
        }
    else:
        raise ValueError(f"unsupported classified double case {case!r}")

    # Exact equality classification replaces the deletion/private-witness
    # relaxation.  Retain both complete point-symmetry quotients.
    cnf, base_metadata = build_double_base(case, False, True)
    graph_points = base_metadata["graph_points"]
    template_metadata = {}
    for color, (template_id, parameters) in template_by_color.items():
        template_metadata[color] = add_template_isomorphism(
            cnf,
            color,
            graph_points[color],
            template_id,
            parameters,
        )
    return cnf, {
        "case": case,
        "first_template": first_template,
        "second_template": second_template,
        "base_metadata": base_metadata,
        "templates": template_metadata,
    }


def render(case: str, first_template: str, second_template: str) -> str:
    cnf, metadata = build_instance(case, first_template, second_template)
    lines = [
        "c ERDOS617 local L=208 classified two-exception branch, version 1",
        (
            f"c case={case} first_template={metadata['first_template']} "
            f"second_template={metadata['second_template']}"
        ),
        "c exact Kang--Pikhurko equality templates via true-twin quotients",
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
    parser.add_argument("--first-template", required=True)
    parser.add_argument("--second-template", required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(
        render(args.case, args.first_template, args.second_template),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

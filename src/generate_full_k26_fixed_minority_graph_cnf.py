#!/usr/bin/env python3
"""Fix a described minority graph and generate its exact four-color extension CNF."""

from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path

from generate_full_k26_cnf import COLORS, ORDER, variable
from generate_full_k26_minority59_cnf import BASE_CLAUSES, base_clauses


def load_graph(path: Path) -> set[tuple[int, int]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("format") != "erdos617-minority-graph-v1" or data.get("order") != ORDER:
        raise ValueError("unsupported minority-graph description")
    components = data.get("components")
    if not isinstance(components, dict):
        raise ValueError("missing graph components")
    cliques = components.get("cliques")
    cycle = components.get("clique_blowup_cycle")
    complement_residual = components.get("complement_residual")
    if not isinstance(cliques, list):
        raise ValueError("malformed graph components")
    if (cycle is None) == (complement_residual is None):
        raise ValueError("graph must select exactly one residual representation")
    if cycle is None and not isinstance(complement_residual, dict):
        raise ValueError("malformed graph components")
    if cycle is not None and (not isinstance(cycle, list) or len(cycle) != 5):
        raise ValueError("malformed graph components")

    if cycle is None:
        residual = complement_residual.get("vertices")
        listed_nonedges = complement_residual.get("nonedges")
        if not isinstance(residual, list) or not isinstance(listed_nonedges, list):
            raise ValueError("malformed complement residual")
        parts = cliques + [residual]
        flattened = [vertex for part in parts for vertex in part]
        if sorted(flattened) != list(range(ORDER)) or len(set(flattened)) != ORDER:
            raise ValueError("graph parts do not partition the vertex set")
        if any(not isinstance(part, list) or not part for part in parts):
            raise ValueError("graph parts must be nonempty lists")
        residual_set = set(residual)
        nonedges = [tuple(pair) for pair in listed_nonedges]
        if (
            any(
                len(pair) != 2
                or pair[0] >= pair[1]
                or pair[0] not in residual_set
                or pair[1] not in residual_set
                for pair in nonedges
            )
            or len(set(nonedges)) != len(nonedges)
        ):
            raise ValueError("malformed complement-residual nonedges")
        edges: set[tuple[int, int]] = set()
        for clique in cliques:
            edges.update(itertools.combinations(sorted(clique), 2))
        edges.update(set(itertools.combinations(sorted(residual), 2)) - set(nonedges))
        return edges

    parts = cliques + cycle
    flattened = [vertex for part in parts for vertex in part]
    if sorted(flattened) != list(range(ORDER)) or len(set(flattened)) != ORDER:
        raise ValueError("graph parts do not partition the vertex set")
    if any(not isinstance(part, list) or not part for part in parts):
        raise ValueError("graph parts must be nonempty lists")

    edges: set[tuple[int, int]] = set()
    for part in parts:
        edges.update(itertools.combinations(sorted(part), 2))
    for index, first in enumerate(cycle):
        second = cycle[(index + 1) % len(cycle)]
        edges.update(tuple(sorted((left, right))) for left in first for right in second)
    return edges


def canonical_remaining_color_clauses():
    """Name colors 1,...,4 in order of their first occurrence."""

    edges = tuple(itertools.combinations(range(ORDER), 2))
    for index, (left, right) in enumerate(edges):
        for color in range(2, COLORS):
            yield [
                -variable(left, right, color),
                *[
                    variable(first, second, color - 1)
                    for first, second in edges[:index]
                ],
            ]


CANONICAL_CLAUSES = math.comb(ORDER, 2) * (COLORS - 2)


def expected_counts() -> tuple[int, int]:
    return (
        math.comb(ORDER, 2) * COLORS,
        BASE_CLAUSES + math.comb(ORDER, 2) + CANONICAL_CLAUSES,
    )


def render(
    graph_path: Path, output: Path, expected_edges: int = 60
) -> tuple[int, int, int]:
    fixed = load_graph(graph_path)
    if len(fixed) != expected_edges:
        raise ValueError(
            f"minority graph has {len(fixed)} edges rather than {expected_edges}"
        )
    variables, clause_count = expected_counts()
    with output.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(
            f"c ERDOS617 fixed exact-{expected_edges} minority-graph extension, version 1\n"
        )
        stream.write(f"c graph={graph_path.name} fixed_color_zero=1 canonical_remaining_colors=1\n")
        stream.write(f"p cnf {variables} {clause_count}\n")
        observed = 0
        for clause in base_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for left, right in itertools.combinations(range(ORDER), 2):
            literal = variable(left, right, 0)
            stream.write(f"{literal if (left, right) in fixed else -literal} 0\n")
            observed += 1
        for clause in canonical_remaining_color_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    return variables, clause_count, len(fixed)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--graph", type=Path, required=True)
    parser.add_argument("--expected-edges", type=int, default=60)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, edges = render(args.graph, args.output, args.expected_edges)
    print(
        "FULL-K26-FIXED-MINORITY-GRAPH-CNF-PASS "
        f"edges={edges} variables={variables} clauses={clauses}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

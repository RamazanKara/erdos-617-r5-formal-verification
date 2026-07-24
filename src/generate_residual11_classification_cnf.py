#!/usr/bin/env python3
"""Classify the final 11-vertex complement after three forced K5 components."""

from __future__ import annotations

import argparse
import itertools
import math
from pathlib import Path

from generate_local_204_cnf import CNF

ORDER = 11
NEIGHBORS = tuple(range(1, 6))
NONNEIGHBORS = tuple(range(6, 11))
EDGE_COUNT = 25


def edge_index(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < ORDER:
        raise ValueError("residual edge endpoints out of range")
    return left * (2 * ORDER - left - 1) // 2 + right - left - 1


def variable(left: int, right: int) -> int:
    return edge_index(left, right) + 1


PHYSICAL_VARIABLES = math.comb(ORDER, 2)


def residual_candidate_edges() -> set[tuple[int, int]]:
    """The triangle-free C5 blow-up complementary to sizes (1,3,2,2,3)."""

    # Build the committed color residual first, then complement it.  Its
    # quotient is a five-cycle with clique parts of sizes (1,3,2,2,3).
    color_parts = ((0,), (1, 2, 3), (4, 5), (6, 7), (8, 9, 10))
    color_edges: set[tuple[int, int]] = set()
    for part in color_parts:
        color_edges.update(itertools.combinations(part, 2))
    for index, first in enumerate(color_parts):
        second = color_parts[(index + 1) % len(color_parts)]
        color_edges.update(
            tuple(sorted((left, right))) for left in first for right in second
        )
    edges = set(itertools.combinations(range(ORDER), 2)) - color_edges
    if len(edges) != EDGE_COUNT:
        raise AssertionError("residual C5 blow-up has wrong edge count")
    return edges


def relabel_edges(
    edges: set[tuple[int, int]], mapping: dict[int, int]
) -> frozenset[tuple[int, int]]:
    return frozenset(
        tuple(sorted((mapping[left], mapping[right]))) for left, right in edges
    )


def candidate_fixed_vertex_orbit() -> tuple[frozenset[tuple[int, int]], ...]:
    """All distinct candidate labelings with N(0)={1,...,5}."""

    edges = residual_candidate_edges()
    adjacency = [set() for _ in range(ORDER)]
    for left, right in edges:
        adjacency[left].add(right)
        adjacency[right].add(left)
    orbit: set[frozenset[tuple[int, int]]] = set()
    for selected in range(ORDER):
        if len(adjacency[selected]) != 5:
            continue
        old_neighbors = tuple(sorted(adjacency[selected]))
        old_non = tuple(
            vertex
            for vertex in range(ORDER)
            if vertex != selected and vertex not in adjacency[selected]
        )
        for neighbor_order in itertools.permutations(old_neighbors):
            neighbor_map = dict(zip(neighbor_order, NEIGHBORS, strict=True))
            for non_order in itertools.permutations(old_non):
                mapping = {selected: 0, **neighbor_map}
                mapping.update(zip(non_order, NONNEIGHBORS, strict=True))
                orbit.add(relabel_edges(edges, mapping))
    result = tuple(sorted(orbit, key=lambda item: tuple(sorted(item))))
    if len(result) != 300:
        raise AssertionError(f"residual candidate orbit has {len(result)} labelings")
    return result


def build_formula() -> tuple[CNF, dict[str, int]]:
    cnf = CNF(variables=PHYSICAL_VARIABLES)
    metadata = {
        "triangle_clauses": 0,
        "independent_six_clauses": 0,
        "maximum_degree_clauses": 0,
        "fixed_neighborhood_units": 0,
        "maximality_witnesses": 0,
        "maximality_clauses": 0,
        "orbit_blocks": 0,
    }

    for first, second, third in itertools.combinations(range(ORDER), 3):
        cnf.add(
            -variable(first, second),
            -variable(first, third),
            -variable(second, third),
        )
        metadata["triangle_clauses"] += 1

    for subset in itertools.combinations(range(ORDER), 6):
        cnf.add(
            *[
                variable(left, right)
                for left, right in itertools.combinations(subset, 2)
            ]
        )
        metadata["independent_six_clauses"] += 1

    all_edges = [
        variable(left, right)
        for left, right in itertools.combinations(range(ORDER), 2)
    ]
    cnf.exactly_k(all_edges, EDGE_COUNT, ("residual-edge-count", EDGE_COUNT))

    for vertex in range(ORDER):
        incident = [variable(vertex, other) for other in range(ORDER) if other != vertex]
        for six in itertools.combinations(incident, 6):
            cnf.add(*[-literal for literal in six])
            metadata["maximum_degree_clauses"] += 1

    for vertex in NEIGHBORS:
        cnf.add(variable(0, vertex))
        metadata["fixed_neighborhood_units"] += 1
    for vertex in NONNEIGHBORS:
        cnf.add(-variable(0, vertex))
        metadata["fixed_neighborhood_units"] += 1

    for left, right in itertools.combinations(range(ORDER), 2):
        witnesses = []
        for point in range(ORDER):
            if point in (left, right):
                continue
            witness = cnf.variable("common-neighbor", left, right, point)
            witnesses.append(witness)
            cnf.add(-witness, variable(left, point))
            cnf.add(-witness, variable(right, point))
            cnf.add(
                witness,
                -variable(left, point),
                -variable(right, point),
            )
            metadata["maximality_witnesses"] += 1
        cnf.add(variable(left, right), *witnesses)
        metadata["maximality_clauses"] += 1

    physical_edges = tuple(itertools.combinations(range(ORDER), 2))
    for candidate in candidate_fixed_vertex_orbit():
        cnf.add(
            *[
                -variable(left, right)
                if (left, right) in candidate
                else variable(left, right)
                for left, right in physical_edges
            ]
        )
        metadata["orbit_blocks"] += 1

    return cnf, metadata


def expected_counts() -> tuple[int, int]:
    cnf, _ = build_formula()
    return cnf.variables, len(cnf.clauses)


def render(path: Path) -> tuple[int, int]:
    cnf, metadata = build_formula()
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 residual order-11 classification complement, version 1\n")
        stream.write("c fixed_degree_five_vertex=0 candidate_orbit_blocked=300\n")
        stream.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    if metadata != {
        "triangle_clauses": 165,
        "independent_six_clauses": 462,
        "maximum_degree_clauses": 2_310,
        "fixed_neighborhood_units": 10,
        "maximality_witnesses": 495,
        "maximality_clauses": 55,
        "orbit_blocks": 300,
    }:
        raise AssertionError(f"residual classification dimensions changed: {metadata}")
    return cnf.variables, len(cnf.clauses)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.output)
    print(
        "RESIDUAL11-CLASSIFICATION-CNF-PASS "
        f"variables={variables} clauses={clauses} orbit_blocks=300"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

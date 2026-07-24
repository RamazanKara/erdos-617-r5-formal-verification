#!/usr/bin/env python3
"""Classify the 12-vertex complement residual in the exact-63 K4 route."""

from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path

from generate_full_k26_min_degree_branch_cnf import add_at_least_k
from generate_local_204_cnf import CNF

ORDER = 12
EDGE_COUNT = 29
MAXIMUM_DEGREE = 5
MINIMUM_DEGREES = (3, 4)
PHYSICAL_EDGES = tuple(itertools.combinations(range(ORDER), 2))


def edge_index(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < ORDER:
        raise ValueError("residual12 edge endpoints out of range")
    return left * (2 * ORDER - left - 1) // 2 + right - left - 1


def variable(left: int, right: int) -> int:
    return edge_index(left, right) + 1


def relabel_edges(
    edges: frozenset[tuple[int, int]], mapping: dict[int, int]
) -> frozenset[tuple[int, int]]:
    return frozenset(
        tuple(sorted((mapping[left], mapping[right]))) for left, right in edges
    )


def fixed_vertex_orbit(
    edges: frozenset[tuple[int, int]], degree: int
) -> tuple[frozenset[tuple[int, int]], ...]:
    adjacency = [set() for _ in range(ORDER)]
    for left, right in edges:
        adjacency[left].add(right)
        adjacency[right].add(left)
    fixed_neighbors = tuple(range(1, degree + 1))
    fixed_non = tuple(range(degree + 1, ORDER))
    orbit = set()
    for selected in range(ORDER):
        if len(adjacency[selected]) != degree:
            continue
        old_neighbors = tuple(sorted(adjacency[selected]))
        old_non = tuple(
            point
            for point in range(ORDER)
            if point != selected and point not in adjacency[selected]
        )
        for neighbor_order in itertools.permutations(old_neighbors):
            neighbor_map = dict(zip(neighbor_order, fixed_neighbors, strict=True))
            for non_order in itertools.permutations(old_non):
                mapping = {selected: 0, **neighbor_map}
                mapping.update(zip(non_order, fixed_non, strict=True))
                orbit.add(relabel_edges(edges, mapping))
    return tuple(sorted(orbit, key=lambda graph: tuple(sorted(graph))))


def load_candidate(path: Path) -> frozenset[tuple[int, int]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if (
        payload.get("version") != 1
        or payload.get("family") != "minority63-k4-route-residual12-complement"
        or payload.get("order") != ORDER
        or payload.get("edge_count") != EDGE_COUNT
    ):
        raise ValueError("candidate does not match the exact-63 residual12 family")
    listed = payload.get("edges")
    if not isinstance(listed, list) or len(listed) != EDGE_COUNT:
        raise ValueError("candidate has the wrong edge count")
    edges = []
    for item in listed:
        if (
            not isinstance(item, list)
            or len(item) != 2
            or not all(isinstance(point, int) for point in item)
            or not 0 <= item[0] < item[1] < ORDER
        ):
            raise ValueError("candidate has a malformed edge")
        edges.append(tuple(item))
    parsed = frozenset(edges)
    if len(parsed) != len(edges):
        raise ValueError("candidate has duplicate edges")
    return parsed


def build_formula(
    minimum_degree: int,
    blocked_candidates: tuple[frozenset[tuple[int, int]], ...] = (),
) -> tuple[CNF, dict[str, int]]:
    if minimum_degree not in MINIMUM_DEGREES:
        raise ValueError("residual12 minimum degree must be three or four")
    cnf = CNF(variables=math.comb(ORDER, 2))
    metadata = {
        "triangle_clauses": 0,
        "independent_six_clauses": 0,
        "maximum_degree_clauses": 0,
        "minimum_degree_constraints": 0,
        "fixed_neighborhood_units": 0,
        "maximality_witnesses": 0,
        "maximality_clauses": 0,
        "blocked_orbit_clauses": 0,
    }
    for triple in itertools.combinations(range(ORDER), 3):
        cnf.add(*[-variable(left, right) for left, right in itertools.combinations(triple, 2)])
        metadata["triangle_clauses"] += 1
    for subset in itertools.combinations(range(ORDER), 6):
        cnf.add(*[variable(left, right) for left, right in itertools.combinations(subset, 2)])
        metadata["independent_six_clauses"] += 1
    cnf.exactly_k(
        [variable(left, right) for left, right in PHYSICAL_EDGES],
        EDGE_COUNT,
        ("minority63-residual12-edges", EDGE_COUNT),
    )
    for point in range(ORDER):
        incident = [variable(point, other) for other in range(ORDER) if other != point]
        for forbidden in itertools.combinations(incident, MAXIMUM_DEGREE + 1):
            cnf.add(*[-literal for literal in forbidden])
            metadata["maximum_degree_clauses"] += 1
        add_at_least_k(
            cnf,
            incident,
            minimum_degree,
            ("minority63-residual12-minimum-degree", minimum_degree, point),
        )
        metadata["minimum_degree_constraints"] += 1
    for point in range(1, ORDER):
        cnf.add(variable(0, point) if point <= minimum_degree else -variable(0, point))
        metadata["fixed_neighborhood_units"] += 1
    for left, right in PHYSICAL_EDGES:
        witnesses = []
        for point in range(ORDER):
            if point in (left, right):
                continue
            witness = cnf.variable("common-neighbor", left, right, point)
            witnesses.append(witness)
            cnf.add(-witness, variable(left, point))
            cnf.add(-witness, variable(right, point))
            cnf.add(witness, -variable(left, point), -variable(right, point))
            metadata["maximality_witnesses"] += 1
        cnf.add(variable(left, right), *witnesses)
        metadata["maximality_clauses"] += 1
    blocked = set()
    for candidate in blocked_candidates:
        blocked.update(fixed_vertex_orbit(candidate, minimum_degree))
    for candidate in sorted(blocked, key=lambda graph: tuple(sorted(graph))):
        cnf.add(
            *[
                -variable(left, right)
                if (left, right) in candidate
                else variable(left, right)
                for left, right in PHYSICAL_EDGES
            ]
        )
        metadata["blocked_orbit_clauses"] += 1
    return cnf, metadata


def render(
    minimum_degree: int,
    path: Path,
    blocked_candidates: tuple[frozenset[tuple[int, int]], ...] = (),
) -> tuple[int, int, dict[str, int]]:
    cnf, metadata = build_formula(minimum_degree, blocked_candidates)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact-63 residual12 complement, version 1\n")
        stream.write(
            f"c order=12 edges=29 fixed_minimum_degree={minimum_degree} "
            f"blocked_orbit={metadata['blocked_orbit_clauses']}\n"
        )
        stream.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    return cnf.variables, len(cnf.clauses), metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--minimum-degree", type=int, choices=MINIMUM_DEGREES, required=True)
    parser.add_argument("--block-json", action="append", default=[], type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    candidates = tuple(load_candidate(path) for path in args.block_json)
    variables, clauses, metadata = render(args.minimum_degree, args.output, candidates)
    print(
        "MINORITY63-RESIDUAL12-CNF-PASS "
        f"degree={args.minimum_degree} variables={variables} clauses={clauses} "
        f"blocked_orbit={metadata['blocked_orbit_clauses']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

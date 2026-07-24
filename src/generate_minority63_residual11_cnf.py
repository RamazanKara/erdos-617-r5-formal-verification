#!/usr/bin/env python3
"""Classify the 11-vertex complement residual in the exact-63 K5 route."""

from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path

from generate_full_k26_min_degree_branch_cnf import add_at_least_k
from generate_local_204_cnf import CNF

ORDER = 11
EDGE_COUNT = 22
MAXIMUM_DEGREE = 5
MINIMUM_DEGREES = (2, 3, 4)
PHYSICAL_EDGES = tuple(itertools.combinations(range(ORDER), 2))


def variable(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < ORDER:
        raise ValueError("residual11 edge endpoints out of range")
    return left * (2 * ORDER - left - 1) // 2 + right - left


def relabel(
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
    orbit = set()
    for selected in range(ORDER):
        if len(adjacency[selected]) != degree:
            continue
        neighbors = tuple(sorted(adjacency[selected]))
        nonneighbors = tuple(
            point
            for point in range(ORDER)
            if point != selected and point not in adjacency[selected]
        )
        for first in itertools.permutations(neighbors):
            partial = {selected: 0, **dict(zip(first, range(1, degree + 1), strict=True))}
            for second in itertools.permutations(nonneighbors):
                mapping = dict(partial)
                mapping.update(zip(second, range(degree + 1, ORDER), strict=True))
                orbit.add(relabel(edges, mapping))
    return tuple(sorted(orbit, key=lambda graph: tuple(sorted(graph))))


def load_candidate(path: Path) -> frozenset[tuple[int, int]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if (
        payload.get("version") != 1
        or payload.get("family") != "minority63-k5-route-residual11-complement"
        or payload.get("order") != ORDER
        or payload.get("edge_count") != EDGE_COUNT
    ):
        raise ValueError("candidate does not match the exact-63 residual11 family")
    listed = payload.get("edges")
    if not isinstance(listed, list) or len(listed) != EDGE_COUNT:
        raise ValueError("candidate has the wrong edge count")
    parsed = []
    for edge in listed:
        if (
            not isinstance(edge, list)
            or len(edge) != 2
            or not all(isinstance(point, int) for point in edge)
            or not 0 <= edge[0] < edge[1] < ORDER
        ):
            raise ValueError("candidate has a malformed edge")
        parsed.append(tuple(edge))
    edges = frozenset(parsed)
    if len(edges) != len(parsed):
        raise ValueError("candidate has duplicate edges")
    return edges


def build_formula(
    minimum_degree: int,
    blocked_candidates: tuple[frozenset[tuple[int, int]], ...] = (),
) -> tuple[CNF, dict[str, int]]:
    if minimum_degree not in MINIMUM_DEGREES:
        raise ValueError("residual11 minimum degree must be two, three, or four")
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
        ("minority63-residual11-edges", EDGE_COUNT),
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
            ("minority63-residual11-minimum-degree", minimum_degree, point),
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
        stream.write("c ERDOS617 exact-63 residual11 complement, version 1\n")
        stream.write(
            f"c order=11 edges=22 fixed_minimum_degree={minimum_degree} "
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
        "MINORITY63-RESIDUAL11-CNF-PASS "
        f"degree={args.minimum_degree} variables={variables} clauses={clauses} "
        f"blocked_orbit={metadata['blocked_orbit_clauses']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

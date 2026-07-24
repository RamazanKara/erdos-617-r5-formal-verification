#!/usr/bin/env python3
"""Generate the final triangle-free complement residual for exact color count 62."""

from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path
from typing import Iterable

from generate_local_204_cnf import CNF

ORDER = 11
FIXED_DEGREE = 5
EDGE_COUNT = 23
MAXIMUM_DEGREE = 5
NEIGHBORS = tuple(range(1, FIXED_DEGREE + 1))
NONNEIGHBORS = tuple(range(FIXED_DEGREE + 1, ORDER))
PHYSICAL_EDGES = tuple(itertools.combinations(range(ORDER), 2))


def edge_index(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < ORDER:
        raise ValueError("residual edge endpoints out of range")
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
    edges: frozenset[tuple[int, int]],
) -> tuple[frozenset[tuple[int, int]], ...]:
    adjacency = [set() for _ in range(ORDER)]
    for left, right in edges:
        adjacency[left].add(right)
        adjacency[right].add(left)
    orbit: set[frozenset[tuple[int, int]]] = set()
    for selected in range(ORDER):
        if len(adjacency[selected]) != FIXED_DEGREE:
            continue
        old_neighbors = tuple(sorted(adjacency[selected]))
        old_non = tuple(
            point
            for point in range(ORDER)
            if point != selected and point not in adjacency[selected]
        )
        for neighbor_order in itertools.permutations(old_neighbors):
            neighbor_map = dict(zip(neighbor_order, NEIGHBORS, strict=True))
            for non_order in itertools.permutations(old_non):
                mapping = {selected: 0, **neighbor_map}
                mapping.update(zip(non_order, NONNEIGHBORS, strict=True))
                orbit.add(relabel_edges(edges, mapping))
    return tuple(sorted(orbit, key=lambda graph: tuple(sorted(graph))))


def load_candidate(path: Path) -> frozenset[tuple[int, int]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if (
        payload.get("version") != 1
        or payload.get("family") != "minority62-k5-route"
        or payload.get("order") != ORDER
        or payload.get("edge_count") != EDGE_COUNT
        or payload.get("fixed_degree_five_vertex") != 0
    ):
        raise ValueError(f"candidate {path} does not match the exact-62 residual")
    listed = payload.get("edges")
    if not isinstance(listed, list) or len(listed) != EDGE_COUNT:
        raise ValueError(f"candidate {path} has the wrong edge count")
    parsed = []
    for edge in listed:
        if not isinstance(edge, list) or len(edge) != 2:
            raise ValueError(f"candidate {path} has a malformed edge")
        left, right = edge
        if (
            not isinstance(left, int)
            or not isinstance(right, int)
            or not 0 <= left < right < ORDER
        ):
            raise ValueError(f"candidate {path} has a noncanonical edge")
        parsed.append((left, right))
    edges = frozenset(parsed)
    if len(edges) != len(parsed):
        raise ValueError(f"candidate {path} has the wrong edge count")
    return edges


def build_formula(
    blocked_candidates: Iterable[frozenset[tuple[int, int]]] = (),
) -> tuple[CNF, dict[str, int]]:
    cnf = CNF(variables=math.comb(ORDER, 2))
    metadata = {
        "triangle_clauses": 0,
        "independent_six_clauses": 0,
        "maximum_degree_clauses": 0,
        "fixed_neighborhood_units": 0,
        "maximality_witnesses": 0,
        "maximality_clauses": 0,
        "blocked_orbit_clauses": 0,
    }

    for first, second, third in itertools.combinations(range(ORDER), 3):
        cnf.add(-variable(first, second), -variable(first, third), -variable(second, third))
        metadata["triangle_clauses"] += 1
    for subset in itertools.combinations(range(ORDER), 6):
        cnf.add(
            *[
                variable(left, right)
                for left, right in itertools.combinations(subset, 2)
            ]
        )
        metadata["independent_six_clauses"] += 1

    cnf.exactly_k(
        [variable(left, right) for left, right in PHYSICAL_EDGES],
        EDGE_COUNT,
        ("minority62-triangle-residual-edges", EDGE_COUNT),
    )

    for point in range(ORDER):
        incident = [variable(point, other) for other in range(ORDER) if other != point]
        for forbidden in itertools.combinations(incident, MAXIMUM_DEGREE + 1):
            cnf.add(*[-literal for literal in forbidden])
            metadata["maximum_degree_clauses"] += 1

    for point in NEIGHBORS:
        cnf.add(variable(0, point))
        metadata["fixed_neighborhood_units"] += 1
    for point in NONNEIGHBORS:
        cnf.add(-variable(0, point))
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

    blocked: set[frozenset[tuple[int, int]]] = set()
    for candidate in blocked_candidates:
        blocked.update(fixed_vertex_orbit(candidate))
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
    path: Path, blocked_candidates: Iterable[frozenset[tuple[int, int]]] = ()
) -> tuple[int, int, dict[str, int]]:
    cnf, metadata = build_formula(blocked_candidates)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact-62 triangle residual, version 1\n")
        stream.write(
            f"c order={ORDER} fixed_vertex=0 fixed_degree={FIXED_DEGREE} "
            f"edges={EDGE_COUNT} blocked_orbit={metadata['blocked_orbit_clauses']}\n"
        )
        stream.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    return cnf.variables, len(cnf.clauses), metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--block-json", action="append", default=[], type=Path)
    args = parser.parse_args()
    candidates = tuple(load_candidate(path) for path in args.block_json)
    variables, clauses, metadata = render(args.output, candidates)
    print(
        "MINORITY62-TRIANGLE-RESIDUAL-CNF-PASS "
        f"variables={variables} clauses={clauses} "
        f"blocked_orbit={metadata['blocked_orbit_clauses']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

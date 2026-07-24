#!/usr/bin/env python3
"""Generate the two triangle-free residual families in the exact-61 reduction."""

from __future__ import annotations

import argparse
import itertools
import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from generate_local_204_cnf import CNF


@dataclass(frozen=True)
class ResidualSpec:
    name: str
    order: int
    fixed_degree: int
    edge_count: int
    maximum_degree: int

    @property
    def neighbors(self) -> tuple[int, ...]:
        return tuple(range(1, self.fixed_degree + 1))

    @property
    def nonneighbors(self) -> tuple[int, ...]:
        return tuple(range(self.fixed_degree + 1, self.order))


SPECS = {
    "k4-route": ResidualSpec("k4-route", 12, 6, 31, 6),
    "k5-route": ResidualSpec("k5-route", 11, 5, 24, 5),
}


def edge_index(order: int, left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < order:
        raise ValueError("residual edge endpoints out of range")
    return left * (2 * order - left - 1) // 2 + right - left - 1


def variable(spec: ResidualSpec, left: int, right: int) -> int:
    return edge_index(spec.order, left, right) + 1


def relabel_edges(
    edges: frozenset[tuple[int, int]], mapping: dict[int, int]
) -> frozenset[tuple[int, int]]:
    return frozenset(
        tuple(sorted((mapping[left], mapping[right]))) for left, right in edges
    )


def fixed_vertex_orbit(
    spec: ResidualSpec, edges: frozenset[tuple[int, int]]
) -> tuple[frozenset[tuple[int, int]], ...]:
    adjacency = [set() for _ in range(spec.order)]
    for left, right in edges:
        adjacency[left].add(right)
        adjacency[right].add(left)
    orbit: set[frozenset[tuple[int, int]]] = set()
    for selected in range(spec.order):
        if len(adjacency[selected]) != spec.fixed_degree:
            continue
        old_neighbors = tuple(sorted(adjacency[selected]))
        old_non = tuple(
            vertex
            for vertex in range(spec.order)
            if vertex != selected and vertex not in adjacency[selected]
        )
        for neighbor_order in itertools.permutations(old_neighbors):
            neighbor_map = dict(zip(neighbor_order, spec.neighbors, strict=True))
            for non_order in itertools.permutations(old_non):
                mapping = {selected: 0, **neighbor_map}
                mapping.update(zip(non_order, spec.nonneighbors, strict=True))
                orbit.add(relabel_edges(edges, mapping))
    return tuple(sorted(orbit, key=lambda item: tuple(sorted(item))))


def load_candidate(spec: ResidualSpec, path: Path) -> frozenset[tuple[int, int]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("family") != spec.name or payload.get("order") != spec.order:
        raise ValueError(f"candidate {path} does not match family {spec.name}")
    edges = frozenset(tuple(sorted(map(int, edge))) for edge in payload["edges"])
    if len(edges) != spec.edge_count:
        raise ValueError(f"candidate {path} has the wrong edge count")
    return edges


def build_formula(
    spec: ResidualSpec,
    blocked_candidates: Iterable[frozenset[tuple[int, int]]] = (),
) -> tuple[CNF, dict[str, int]]:
    cnf = CNF(variables=math.comb(spec.order, 2))
    metadata = {
        "triangle_clauses": 0,
        "independent_six_clauses": 0,
        "maximum_degree_clauses": 0,
        "fixed_neighborhood_units": 0,
        "maximality_witnesses": 0,
        "maximality_clauses": 0,
        "blocked_orbit_clauses": 0,
    }

    for first, second, third in itertools.combinations(range(spec.order), 3):
        cnf.add(
            -variable(spec, first, second),
            -variable(spec, first, third),
            -variable(spec, second, third),
        )
        metadata["triangle_clauses"] += 1

    for subset in itertools.combinations(range(spec.order), 6):
        cnf.add(
            *[
                variable(spec, left, right)
                for left, right in itertools.combinations(subset, 2)
            ]
        )
        metadata["independent_six_clauses"] += 1

    all_edges = [
        variable(spec, left, right)
        for left, right in itertools.combinations(range(spec.order), 2)
    ]
    cnf.exactly_k(all_edges, spec.edge_count, ("minority61-residual-edges", spec.name))

    forbidden_incident_count = spec.maximum_degree + 1
    for vertex in range(spec.order):
        incident = [
            variable(spec, vertex, other)
            for other in range(spec.order)
            if other != vertex
        ]
        for forbidden in itertools.combinations(incident, forbidden_incident_count):
            cnf.add(*[-literal for literal in forbidden])
            metadata["maximum_degree_clauses"] += 1

    for vertex in spec.neighbors:
        cnf.add(variable(spec, 0, vertex))
        metadata["fixed_neighborhood_units"] += 1
    for vertex in spec.nonneighbors:
        cnf.add(-variable(spec, 0, vertex))
        metadata["fixed_neighborhood_units"] += 1

    for left, right in itertools.combinations(range(spec.order), 2):
        witnesses = []
        for point in range(spec.order):
            if point in (left, right):
                continue
            witness = cnf.variable("common-neighbor", left, right, point)
            witnesses.append(witness)
            cnf.add(-witness, variable(spec, left, point))
            cnf.add(-witness, variable(spec, right, point))
            cnf.add(
                witness,
                -variable(spec, left, point),
                -variable(spec, right, point),
            )
            metadata["maximality_witnesses"] += 1
        cnf.add(variable(spec, left, right), *witnesses)
        metadata["maximality_clauses"] += 1

    physical_edges = tuple(itertools.combinations(range(spec.order), 2))
    blocked: set[frozenset[tuple[int, int]]] = set()
    for candidate in blocked_candidates:
        blocked.update(fixed_vertex_orbit(spec, candidate))
    for candidate in sorted(blocked, key=lambda item: tuple(sorted(item))):
        cnf.add(
            *[
                -variable(spec, left, right)
                if (left, right) in candidate
                else variable(spec, left, right)
                for left, right in physical_edges
            ]
        )
        metadata["blocked_orbit_clauses"] += 1

    return cnf, metadata


def render(
    spec: ResidualSpec,
    path: Path,
    blocked_candidates: Iterable[frozenset[tuple[int, int]]] = (),
) -> tuple[int, int, dict[str, int]]:
    cnf, metadata = build_formula(spec, blocked_candidates)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact-61 triangle residual, version 1\n")
        stream.write(
            f"c family={spec.name} order={spec.order} fixed_vertex=0 "
            f"fixed_degree={spec.fixed_degree} edges={spec.edge_count}"
        )
        if metadata["blocked_orbit_clauses"]:
            stream.write(
                f" blocked_orbit={metadata['blocked_orbit_clauses']}"
            )
        stream.write("\n")
        stream.write(f"p cnf {cnf.variables} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
    return cnf.variables, len(cnf.clauses), metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("family", choices=tuple(SPECS))
    parser.add_argument("output", type=Path)
    parser.add_argument("--block-json", action="append", default=[], type=Path)
    args = parser.parse_args()
    spec = SPECS[args.family]
    blocked_candidates = tuple(load_candidate(spec, path) for path in args.block_json)
    variables, clauses, metadata = render(spec, args.output, blocked_candidates)
    print(
        "MINORITY61-TRIANGLE-RESIDUAL-CNF-PASS "
        f"family={spec.name} variables={variables} clauses={clauses} "
        f"maximality_witnesses={metadata['maximality_witnesses']} "
        f"blocked_orbit={metadata['blocked_orbit_clauses']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

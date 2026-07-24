#!/usr/bin/env python3
"""Generate necessary CNFs for the three one-slack critical E009 profiles."""

from __future__ import annotations

import argparse
import itertools
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_204_cnf import CNF  # noqa: E402
from src.generate_local_205_critical_cnf import (  # noqa: E402
    build_fixed_balanced_instance,
)


PROFILES: dict[str, tuple[int, int, int, tuple[tuple[int, int], ...]]] = {
    # profile: (variable-component order, alpha, edge count, fixed cliques)
    "112-near": (10, 2, 25, ((10, 15), (15, 20))),
    "13-near": (15, 3, 35, ((15, 20),)),
    "4-near": (20, 4, 45, ()),
}


def add_conditional_private_witness(
    cnf: CNF,
    edges: dict[tuple[int, int], int],
    order: int,
    left: int,
    right: int,
    witness_size: int,
) -> int:
    """Make edge left-right critical for independence number witness_size+1."""
    edge = edges[left, right]
    remaining = [point for point in range(order) if point not in (left, right)]
    selectors = [
        cnf.variable("private-witness-vertex", left, right, point)
        for point in remaining
    ]
    first_gated_clause = len(cnf.clauses)
    cnf.exactly_k(
        selectors,
        witness_size,
        ("private-witness-size", left, right),
    )
    for clause in cnf.clauses[first_gated_clause:]:
        clause.append(-edge)
    for point, selector in zip(remaining, selectors, strict=True):
        cnf.add(-selector, edge)
        cnf.add(-selector, -edges[tuple(sorted((left, point)))])
        cnf.add(-selector, -edges[tuple(sorted((right, point)))])
    for first_index, second_index in itertools.combinations(
        range(len(remaining)), 2
    ):
        pair = tuple(sorted((remaining[first_index], remaining[second_index])))
        cnf.add(
            -selectors[first_index],
            -selectors[second_index],
            -edges[pair],
        )
    return len(selectors)


def build_instance(profile: str) -> tuple[CNF, dict[str, object]]:
    if profile not in PROFILES:
        raise ValueError(f"unsupported profile {profile!r}")
    order, alpha, edge_count, fixed_cliques = PROFILES[profile]
    cnf = CNF()
    edges = {
        pair: cnf.variable("exceptional-edge", *pair)
        for pair in itertools.combinations(range(order), 2)
    }

    cnf.exactly_k(
        list(edges.values()),
        edge_count,
        ("exceptional-component-edge-count", profile),
    )
    independent_set_constraints = 0
    for subset in itertools.combinations(range(order), alpha + 1):
        cnf.add(*[edges[pair] for pair in itertools.combinations(subset, 2)])
        independent_set_constraints += 1

    clique_six_constraints = 0
    for subset in itertools.combinations(range(order), 6):
        cnf.add(*[-edges[pair] for pair in itertools.combinations(subset, 2)])
        clique_six_constraints += 1

    witness_selectors = 0
    for left, right in itertools.combinations(range(order), 2):
        witness_selectors += add_conditional_private_witness(
            cnf,
            edges,
            order,
            left,
            right,
            alpha - 1,
        )

    fixed_edges: set[tuple[int, int]] = set()
    for start, stop in fixed_cliques:
        fixed_edges.update(itertools.combinations(range(start, stop), 2))
    cnf, incidence_metadata = build_fixed_balanced_instance(
        fixed_edges,
        cnf=cnf,
        variable_exceptional_edges=edges,
    )
    return cnf, {
        "profile": profile,
        "component_order": order,
        "component_alpha": alpha,
        "component_edge_count": edge_count,
        "component_edge_variables": len(edges),
        "fixed_edges": fixed_edges,
        "independent_set_constraints": independent_set_constraints,
        "clique_six_constraints": clique_six_constraints,
        "private_witness_selectors": witness_selectors,
        "incidence": incidence_metadata,
    }


def render(profile: str) -> str:
    cnf, metadata = build_instance(profile)
    lines = [
        "c ERDOS617 local L=205 edge-critical one-slack compatibility, version 1",
        (
            f"c profile={profile} component_order={metadata['component_order']} "
            f"component_alpha={metadata['component_alpha']} "
            f"component_edges={metadata['component_edge_count']}"
        ),
        (
            f"c edge_variables={metadata['component_edge_variables']} "
            f"independent_set_constraints={metadata['independent_set_constraints']} "
            f"clique_six_constraints={metadata['clique_six_constraints']} "
            f"private_witness_selectors={metadata['private_witness_selectors']}"
        ),
        f"p cnf {cnf.variables} {len(cnf.clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in cnf.clauses)
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--profile", choices=tuple(PROFILES), required=True)
    args = parser.parse_args()
    args.output.write_text(render(args.profile), encoding="ascii", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

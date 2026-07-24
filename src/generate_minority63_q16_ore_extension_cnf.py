#!/usr/bin/env python3
"""Generate one exact unrestricted extension formula for all 48 final Q16 classes."""

from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path

from enumerate_minority63_q16_ore import graph6_decode
from generate_full_k26_cnf import COLORS, ORDER, variable
from generate_full_k26_fixed_minority_graph_cnf import canonical_remaining_color_clauses
from generate_full_k26_minority59_cnf import BASE_CLAUSES, base_clauses
from generate_local_204_cnf import CNF

REPOSITORY = Path(__file__).resolve().parents[1]
DEFAULT_CATALOG = REPOSITORY / "artifacts/minority63_q16_ore_catalog.json"
BASE_VARIABLES = math.comb(ORDER, 2) * COLORS
FIXED_CLIQUES = (tuple(range(0, 5)), tuple(range(5, 10)))
RESIDUAL = tuple(range(10, 26))


def load_catalog(path: Path) -> tuple[frozenset[tuple[int, int]], ...]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if (
        payload.get("version") != 1
        or payload.get("family") != "minority63-q16-6-ore"
        or payload.get("order") != 16
        or payload.get("edge_count") != 43
    ):
        raise ValueError("catalog does not describe the E031 Q16 Ore family")
    encoded = payload.get("graphs")
    if not isinstance(encoded, list) or len(encoded) != 48 or len(set(encoded)) != 48:
        raise ValueError("Q16 Ore catalog must contain 48 distinct graph6 strings")
    graphs = []
    for item in encoded:
        if not isinstance(item, str):
            raise ValueError("Q16 Ore catalog has a non-string graph6 entry")
        order, graph = graph6_decode(item)
        if order != 16 or len(graph) != 43:
            raise ValueError("Q16 Ore catalog graph has wrong dimensions")
        graphs.append(graph)
    return tuple(graphs)


def full_graph(residual_graph: frozenset[tuple[int, int]]) -> frozenset[tuple[int, int]]:
    edges = set()
    for clique in FIXED_CLIQUES:
        edges.update(itertools.combinations(clique, 2))
    edges.update((left + 10, right + 10) for left, right in residual_graph)
    if len(edges) != 63:
        raise AssertionError("Q16 catalog extension does not fix 63 color-zero edges")
    return frozenset(edges)


def build_extension(
    graphs: tuple[frozenset[tuple[int, int]], ...]
) -> tuple[CNF, dict[str, int]]:
    result = CNF(variables=BASE_VARIABLES)
    selectors = [result.variable("minority63-q16-ore-class", index) for index in range(len(graphs))]
    metadata = {
        "classes": len(graphs),
        "selector_variables": len(selectors),
        "selector_at_least_clauses": 0,
        "selector_at_most_clauses": 0,
        "conditional_fixed_units": 0,
        "canonical_remaining_color_clauses": 0,
    }
    result.add(*selectors)
    metadata["selector_at_least_clauses"] += 1
    for first, second in itertools.combinations(selectors, 2):
        result.add(-first, -second)
        metadata["selector_at_most_clauses"] += 1
    physical = tuple(itertools.combinations(range(ORDER), 2))
    for selector, residual_graph in zip(selectors, graphs, strict=True):
        fixed = full_graph(residual_graph)
        for left, right in physical:
            literal = variable(left, right, 0)
            result.add(-selector, literal if (left, right) in fixed else -literal)
            metadata["conditional_fixed_units"] += 1
    for clause in canonical_remaining_color_clauses():
        result.add(*clause)
        metadata["canonical_remaining_color_clauses"] += 1
    return result, metadata


def render(catalog: Path, output: Path) -> tuple[int, int, dict[str, int]]:
    graphs = load_catalog(catalog)
    extension, metadata = build_extension(graphs)
    clause_count = BASE_CLAUSES + len(extension.clauses)
    with output.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact-63 Q16 6-Ore catalog extension, version 1\n")
        stream.write(
            "c q16_classes=48 fixed_k5_components=2 "
            "canonical_remaining_colors=1 unrestricted_remaining_edges=1\n"
        )
        stream.write(f"p cnf {extension.variables} {clause_count}\n")
        observed = 0
        for clause in base_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for clause in extension.clauses:
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    return extension.variables, clause_count, metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--catalog", type=Path, default=DEFAULT_CATALOG)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses, metadata = render(args.catalog, args.output)
    print(
        "MINORITY63-Q16-ORE-EXTENSION-CNF-PASS "
        f"classes={metadata['classes']} variables={variables} clauses={clauses} "
        f"conditional_units={metadata['conditional_fixed_units']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Split the degree-four critical minority graph by its minimum neighborhood."""

from __future__ import annotations

import argparse
from pathlib import Path

from generate_minority60_critical_graph_cnf import (
    BASE_CLAUSES,
    build_extensions,
    graph_base_clauses,
    graph_variable,
)
from generate_local_204_cnf import CNF

BRANCHES = ("nonclique", "clique-leak")


def structural_extension(starting_variables: int, branch: str) -> CNF:
    if branch not in BRANCHES:
        raise ValueError("unknown degree-four structure branch")
    cnf = CNF(variables=starting_variables)
    if branch == "nonclique":
        # Vertices 1 and 6 are two nonadjacent neighbors of the selected
        # minimum-degree vertex 0.  The private witness for edge (0,1) remains
        # vertices 2,...,5, so all labels are compatible.
        cnf.add(graph_variable(0, 6))
        cnf.add(-graph_variable(1, 6))
    else:
        # N(0)={1,6,7,8} is a clique, but its vertex 1 has an edge to an
        # outside vertex 9.  Exact degree four already excludes every other
        # neighbor of 0; the explicit (0,9) nonedge audits that interpretation.
        neighbors = (1, 6, 7, 8)
        for vertex in neighbors:
            cnf.add(graph_variable(0, vertex))
        for index, left in enumerate(neighbors):
            for right in neighbors[index + 1 :]:
                cnf.add(graph_variable(left, right))
        cnf.add(-graph_variable(0, 9))
        cnf.add(graph_variable(1, 9))
    return cnf


def build_formula(branch: str):
    cardinality, degrees, orbit, critical, metadata = build_extensions(4)
    structural = structural_extension(critical.variables, branch)
    return cardinality, degrees, orbit, critical, structural, metadata


def expected_counts(branch: str) -> tuple[int, int]:
    parts = build_formula(branch)[:5]
    return parts[-1].variables, BASE_CLAUSES + sum(len(part.clauses) for part in parts)


def render(branch: str, path: Path) -> tuple[int, int]:
    cardinality, degrees, orbit, critical, structural, _ = build_formula(branch)
    parts = (cardinality, degrees, orbit, critical, structural)
    variables = structural.variables
    clause_count = BASE_CLAUSES + sum(len(part.clauses) for part in parts)
    with path.open("w", encoding="ascii", newline="\n") as stream:
        stream.write("c ERDOS617 exact-60 degree-four structural graph branch, version 1\n")
        stream.write(f"c branch={branch} fixed_private_witness=0,1,2,3,4,5\n")
        stream.write(f"p cnf {variables} {clause_count}\n")
        observed = 0
        for clause in graph_base_clauses():
            stream.write(" ".join(map(str, clause)) + " 0\n")
            observed += 1
        for part in parts:
            for clause in part.clauses:
                stream.write(" ".join(map(str, clause)) + " 0\n")
                observed += 1
    if observed != clause_count:
        raise AssertionError(f"generated {observed} clauses, expected {clause_count}")
    return variables, clause_count


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", choices=BRANCHES, required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    variables, clauses = render(args.branch, args.output)
    print(
        "MINORITY60-DEGREE4-STRUCTURE-CNF-PASS "
        f"branch={args.branch} variables={variables} clauses={clauses}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

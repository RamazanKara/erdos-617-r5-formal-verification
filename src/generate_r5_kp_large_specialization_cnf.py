#!/usr/bin/env python3
"""Generate the six labelled graph CNFs preregistered in E046."""

from __future__ import annotations

import argparse
import itertools
import math
from dataclasses import dataclass
from pathlib import Path

from generate_local_204_cnf import CNF


@dataclass(frozen=True)
class Case:
    order: int
    independence_bound: int
    clique_bound: int
    edge_lower_bound: int


CASES = {
    "r3_n19": Case(19, 3, 5, 56),
    "r3_n20": Case(20, 3, 5, 62),
    "r3_n21": Case(21, 3, 5, 69),
    "r3_n22": Case(22, 3, 5, 76),
    "r4_n24": Case(24, 4, 5, 65),
    "r4_n25": Case(25, 4, 5, 71),
}


def edge_pairs(order: int) -> tuple[tuple[int, int], ...]:
    return tuple(itertools.combinations(range(order), 2))


def build_graph_instance(case: Case, label: str) -> CNF:
    pairs = edge_pairs(case.order)
    cnf = CNF()
    edge = {pair: cnf.variable("edge", *pair) for pair in pairs}

    for vertices in itertools.combinations(
        range(case.order), case.independence_bound + 1
    ):
        cnf.add(*(edge[pair] for pair in itertools.combinations(vertices, 2)))

    for vertices in itertools.combinations(range(case.order), case.clique_bound + 1):
        cnf.add(*(-edge[pair] for pair in itertools.combinations(vertices, 2)))

    cnf.at_most_k(
        [edge[pair] for pair in pairs],
        case.edge_lower_bound - 1,
        ("E046-edge-upper-bound", label),
    )
    return cnf


def build_instance(case_id: str) -> CNF:
    return build_graph_instance(CASES[case_id], case_id)


def render(case_id: str) -> str:
    case = CASES[case_id]
    cnf = build_instance(case_id)
    independence_clauses = math.comb(case.order, case.independence_bound + 1)
    clique_clauses = math.comb(case.order, case.clique_bound + 1)
    lines = [
        "c E046 finite Kang--Pikhurko replacement",
        (
            f"c case={case_id} order={case.order} "
            f"alpha_bound={case.independence_bound} "
            f"omega_bound={case.clique_bound} "
            f"edge_upper_bound={case.edge_lower_bound - 1}"
        ),
        (
            f"c primary_edges={case.order * (case.order - 1) // 2} "
            f"independence_clauses={independence_clauses} "
            f"clique_clauses={clique_clauses}"
        ),
        f"p cnf {cnf.variables} {len(cnf.clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in cnf.clauses)
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", choices=tuple(CASES), required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(render(args.case), encoding="ascii", newline="\n")
    case = CASES[args.case]
    cnf = build_instance(args.case)
    print(
        "R5-KP-LARGE-SPECIALIZATION-CNF-PASS "
        f"case={args.case} order={case.order} "
        f"alpha_bound={case.independence_bound} omega_bound={case.clique_bound} "
        f"edge_upper_bound={case.edge_lower_bound - 1} "
        f"variables={cnf.variables} clauses={len(cnf.clauses)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

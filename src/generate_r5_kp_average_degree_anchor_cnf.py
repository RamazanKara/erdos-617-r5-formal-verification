#!/usr/bin/env python3
"""Generate the six orbit-retaining E047 average-degree anchor CNFs."""

from __future__ import annotations

import argparse
from pathlib import Path

from generate_r5_kp_large_specialization_cnf import CASES, build_instance


def degree_cap(case_id: str) -> int:
    case = CASES[case_id]
    return 2 * (case.edge_lower_bound - 1) // case.order


def build_anchored_instance(case_id: str):
    case = CASES[case_id]
    cap = degree_cap(case_id)
    cnf = build_instance(case_id)
    for earlier, later in zip(range(1, case.order - 1), range(2, case.order)):
        cnf.add(
            cnf.names[("edge", 0, earlier)],
            -cnf.names[("edge", 0, later)],
        )
    cnf.add(-cnf.names[("edge", 0, cap + 1)])
    return cnf


def render(case_id: str) -> str:
    case = CASES[case_id]
    cap = degree_cap(case_id)
    base = build_instance(case_id)
    cnf = build_anchored_instance(case_id)
    lines = [
        "c E047 average-degree anchor quotient",
        (
            f"c case={case_id} order={case.order} "
            f"edge_upper_bound={case.edge_lower_bound - 1} degree_cap={cap}"
        ),
        (
            f"c parent_variables={base.variables} parent_clauses={len(base.clauses)} "
            f"anchor_clauses={case.order - 1}"
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
    cnf = build_anchored_instance(args.case)
    print(
        "R5-KP-AVERAGE-DEGREE-ANCHOR-CNF-PASS "
        f"case={args.case} order={case.order} degree_cap={degree_cap(args.case)} "
        f"variables={cnf.variables} clauses={len(cnf.clauses)} "
        f"anchor_clauses={case.order - 1}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

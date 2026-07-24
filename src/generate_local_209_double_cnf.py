#!/usr/bin/env python3
"""Generate the three E014 same-layout two-exception CNF families."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_208_double_cnf import (  # noqa: E402
    build_instance as build_base,
)

CASES = {
    "balanced_double45_44": ("balanced_double44", {0: 45, 1: 44}),
    "unbalanced_double50_39": ("unbalanced_double49_39", {0: 50, 4: 39}),
    "unbalanced_double49_40": ("unbalanced_double49_39", {0: 49, 4: 40}),
}


def build_instance(
    case: str,
    require_edge_minimality: bool = False,
    fix_second_resolution_free_group: bool = False,
    edge_minimality_colors: tuple[int, ...] | None = None,
):
    if case not in CASES:
        raise ValueError(f"unsupported local-209 double case {case!r}")
    base_case, edge_counts = CASES[case]
    cnf, metadata = build_base(
        base_case,
        require_edge_minimality,
        fix_second_resolution_free_group,
        edge_counts,
        edge_minimality_colors,
    )
    metadata = dict(metadata)
    metadata["case"] = case
    return cnf, metadata


def render(
    case: str,
    require_edge_minimality: bool = False,
    fix_second_resolution_free_group: bool = False,
) -> str:
    cnf, metadata = build_instance(
        case,
        require_edge_minimality,
        fix_second_resolution_free_group,
    )
    exceptional_colors = metadata["exceptional_colors"]
    edge_counts = metadata["exceptional_edge_counts"]
    orders = {
        color: len(metadata["graph_points"][color])
        for color in exceptional_colors
    }
    lines = [
        "c ERDOS617 local L=209 same-layout two-exception compatibility, version 1",
        (
            f"c case={case} exceptional_colors="
            + ",".join(map(str, exceptional_colors))
            + " exceptional_orders="
            + ",".join(str(orders[color]) for color in exceptional_colors)
            + " exceptional_edges="
            + ",".join(str(edge_counts[color]) for color in exceptional_colors)
            + " alpha<=4 omega<=5"
        ),
        (
            "c edge_minimality="
            f"{int(require_edge_minimality)} fixed_resolution_memberships="
            f"{metadata['fixed_resolution_memberships']} "
            "fixed_free_group_memberships="
            f"{metadata['fixed_free_group_memberships']} "
            "common_exceptional_pairs="
            f"{metadata['common_exceptional_pairs']}"
        ),
        f"p cnf {cnf.variables} {len(cnf.clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in cnf.clauses)
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", choices=tuple(CASES), required=True)
    parser.add_argument("--minimal", action="store_true")
    parser.add_argument("--fix-second-resolution-free-group", action="store_true")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(
        render(
            args.case,
            args.minimal,
            args.fix_second_resolution_free_group,
        ),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

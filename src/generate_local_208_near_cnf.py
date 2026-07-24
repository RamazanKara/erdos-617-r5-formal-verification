#!/usr/bin/env python3
"""Generate classification-free one-exception CNFs at local count 208."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_205_near_cnf import (  # noqa: E402
    build_instance as build_balanced_base,
)
from src.generate_local_206_near_cnf import (  # noqa: E402
    build_unbalanced,
    parse_resolution_four_profile,
)


def build_instance(
    case: str,
    require_edge_minimality: bool = False,
    require_forced_compositions: bool = False,
    resolution_four_profile: tuple[int, int, int, int] | None = None,
    fix_resolution_two_group_one: bool = False,
):
    if case == "balanced48":
        if require_forced_compositions or resolution_four_profile is not None:
            raise ValueError("balanced48 already encodes every forced composition")
        cnf, metadata = build_balanced_base(
            require_edge_minimality=require_edge_minimality,
            exceptional_edge_count=48,
            fix_resolution_two_group_one=fix_resolution_two_group_one,
        )
        metadata = dict(metadata)
        metadata["case"] = case
        return cnf, metadata
    if case == "unbalanced52":
        return build_unbalanced(
            require_edge_minimality,
            require_forced_compositions,
            resolution_four_profile,
            fix_resolution_two_group_one,
            52,
        )
    raise ValueError(f"unsupported local-208 near case {case!r}")


def render(
    case: str,
    require_edge_minimality: bool = False,
    require_forced_compositions: bool = False,
    resolution_four_profile: tuple[int, int, int, int] | None = None,
    fix_resolution_two_group_one: bool = False,
) -> str:
    cnf, metadata = build_instance(
        case,
        require_edge_minimality,
        require_forced_compositions,
        resolution_four_profile,
        fix_resolution_two_group_one,
    )
    order = 20 if case == "balanced48" else 21
    lines = [
        "c ERDOS617 local L=208 one-exception compatibility, version 1",
        (
            f"c case={case} exceptional_order={order} "
            f"exceptional_edges={metadata['exceptional_edge_count']} "
            "alpha<=4 omega<=5"
        ),
        (
            f"c exceptional_variables={metadata['exceptional_variables']} "
            f"five_sets={metadata['five_sets']} six_sets={metadata['six_sets']} "
            f"fixed_resolution_memberships="
            f"{metadata['fixed_resolution_memberships']} "
            f"private_witness_selectors="
            f"{metadata['private_witness_selectors']} "
            f"forced_compositions="
            f"{int(bool(metadata.get('forced_compositions', False)))} "
            "resolution_four_profile="
            + (
                "none"
                if metadata.get("resolution_four_profile") is None
                else ",".join(map(str, metadata["resolution_four_profile"]))
            )
            + " fixed_resolution_two_group_one="
            + str(int(bool(metadata.get("fixed_resolution_two_group_one", False))))
        ),
        f"p cnf {cnf.variables} {len(cnf.clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in cnf.clauses)
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--case", choices=("balanced48", "unbalanced52"), required=True
    )
    parser.add_argument("--minimal", action="store_true")
    parser.add_argument("--forced-compositions", action="store_true")
    parser.add_argument(
        "--resolution-four-profile", type=parse_resolution_four_profile
    )
    parser.add_argument("--fix-resolution-two-group-one", action="store_true")
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(
        render(
            args.case,
            args.minimal,
            args.forced_compositions,
            args.resolution_four_profile,
            args.fix_resolution_two_group_one,
        ),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

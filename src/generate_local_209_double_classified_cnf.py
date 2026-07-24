#!/usr/bin/env python3
"""Generate the exhaustive classified E014 double-exception branches."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_208_double_classified_cnf import (  # noqa: E402
    add_template_isomorphism,
    template_catalogs,
)
from src.generate_local_209_double_cnf import (  # noqa: E402
    build_instance as build_same_layout,
)
from src.generate_local_209_mixed_double_cnf import (  # noqa: E402
    build_instance as build_mixed,
)


VARIABLE_45 = "variable45"
VARIABLE_50 = "variable50"
VARIABLE_40 = "variable40"


def branch_catalog() -> list[tuple[str, str, str]]:
    balanced, order_21, order_19 = template_catalogs()
    branches = [
        ("balanced_double45_44", VARIABLE_45, template)
        for template in balanced
    ]
    branches.extend(
        ("unbalanced_double50_39", VARIABLE_50, template)
        for template in order_19
    )
    branches.extend(
        ("unbalanced_double49_40", template, VARIABLE_40)
        for template in order_21
    )
    branches.extend(
        ("unbalanced_double49_44", first, second)
        for first in order_21
        for second in balanced
    )
    if len(branches) != 16:
        raise AssertionError("wrong E014 classified branch count")
    return branches


def build_instance(case: str, first_template: str, second_template: str):
    balanced, order_21, order_19 = template_catalogs()
    template_by_color = {}
    if case == "balanced_double45_44":
        if first_template != VARIABLE_45 or second_template not in balanced:
            raise ValueError("unknown balanced 45/44 classified branch")
        cnf, base_metadata = build_same_layout(
            case,
            False,
            True,
            (0,),
        )
        template_by_color[1] = (second_template, balanced[second_template])
    elif case == "unbalanced_double50_39":
        if first_template != VARIABLE_50 or second_template not in order_19:
            raise ValueError("unknown unbalanced 50/39 classified branch")
        cnf, base_metadata = build_same_layout(
            case,
            False,
            True,
            (0,),
        )
        template_by_color[4] = (second_template, order_19[second_template])
    elif case == "unbalanced_double49_40":
        if first_template not in order_21 or second_template != VARIABLE_40:
            raise ValueError("unknown unbalanced 49/40 classified branch")
        cnf, base_metadata = build_same_layout(
            case,
            False,
            True,
            (4,),
        )
        template_by_color[0] = (first_template, order_21[first_template])
    elif case == "unbalanced_double49_44":
        if first_template not in order_21 or second_template not in balanced:
            raise ValueError("unknown mixed 49/44 classified branch")
        cnf, base_metadata = build_mixed(False, True, ())
        template_by_color = {
            0: (first_template, order_21[first_template]),
            1: (second_template, balanced[second_template]),
        }
    else:
        raise ValueError(f"unsupported E014 classified case {case!r}")

    graph_points = base_metadata["graph_points"]
    template_metadata = {}
    for color, (template_id, parameters) in template_by_color.items():
        template_metadata[color] = add_template_isomorphism(
            cnf,
            color,
            graph_points[color],
            template_id,
            parameters,
        )
    return cnf, {
        "case": case,
        "first_template": first_template,
        "second_template": second_template,
        "base_metadata": base_metadata,
        "templates": template_metadata,
    }


def render(case: str, first_template: str, second_template: str) -> str:
    cnf, metadata = build_instance(case, first_template, second_template)
    lines = [
        "c ERDOS617 local L=209 classified two-exception branch, version 1",
        (
            f"c case={case} first_template={metadata['first_template']} "
            f"second_template={metadata['second_template']}"
        ),
        "c exact equality templates via true-twin quotients",
        f"p cnf {cnf.variables} {len(cnf.clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in cnf.clauses)
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--case",
        choices=(
            "balanced_double45_44",
            "unbalanced_double50_39",
            "unbalanced_double49_40",
            "unbalanced_double49_44",
        ),
        required=True,
    )
    parser.add_argument("--first-template", required=True)
    parser.add_argument("--second-template", required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(
        render(args.case, args.first_template, args.second_template),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

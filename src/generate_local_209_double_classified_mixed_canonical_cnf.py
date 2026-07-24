#!/usr/bin/env python3
"""Representation quotients for classified E014 mixed 49/44 branches."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_208_double_classified_cnf import template_catalogs  # noqa: E402
from src.generate_local_209_double_classified_cnf import (  # noqa: E402
    build_instance as build_classified,
)

CASE = "unbalanced_double49_44"
ORDERED_CLASSES = (4, 5)


def catalogs():
    balanced, order_21, _ = template_catalogs()
    return tuple(order_21), tuple(balanced)


def build_instance(first_template: str, second_template: str):
    order_21, order_20 = catalogs()
    if first_template not in order_21 or second_template not in order_20:
        raise ValueError("unsupported mixed classified template pair")
    cnf, base_metadata = build_classified(CASE, first_template, second_template)
    template_by_color = {0: first_template, 1: second_template}
    graph_points = base_metadata["base_metadata"]["graph_points"]
    for color, template in template_by_color.items():
        first = [
            cnf.names[(
                "exceptional-template-class",
                color,
                template,
                ORDERED_CLASSES[0],
                point,
            )]
            for point in graph_points[color]
        ]
        second = [
            cnf.names[(
                "exceptional-template-class",
                color,
                template,
                ORDERED_CLASSES[1],
                point,
            )]
            for point in graph_points[color]
        ]
        cnf.lexicographic_leq(
            first,
            second,
            ("template-class-order", color, *ORDERED_CLASSES),
        )
    return cnf, {
        "case": CASE,
        "first_template": first_template,
        "second_template": second_template,
        "ordered_classes": ORDERED_CLASSES,
        "ordered_colors": (0, 1),
        "base_metadata": base_metadata,
    }


def render(first_template: str, second_template: str) -> str:
    cnf, metadata = build_instance(first_template, second_template)
    lines = [
        "c ERDOS617 local L=209 classified mixed canonical quotient, version 1",
        (
            f"c case={CASE} first_template={metadata['first_template']} "
            f"second_template={metadata['second_template']} twin_class_orders=2"
        ),
        "c each class 4/5 swap is a template-representation automorphism",
        f"p cnf {cnf.variables} {len(cnf.clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in cnf.clauses)
    return "\n".join(lines) + "\n"


def main() -> int:
    order_21, order_20 = catalogs()
    parser = argparse.ArgumentParser()
    parser.add_argument("--first-template", choices=order_21, required=True)
    parser.add_argument("--second-template", choices=order_20, required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(
        render(args.first_template, args.second_template),
        encoding="ascii",
        newline="\n",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

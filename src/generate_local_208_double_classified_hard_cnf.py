#!/usr/bin/env python3
"""Canonical repair input for the sole undecided E013 classified branch."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_208_double_classified_cnf import (  # noqa: E402
    build_instance as build_classified,
)

CASE = "balanced_double44"
TEMPLATE = "b4555_large_a2"


def build_instance():
    cnf, base_metadata = build_classified(CASE, TEMPLATE, TEMPLATE)
    graph_points = base_metadata["base_metadata"]["graph_points"]
    ordered_classes = (4, 5)
    for color in (0, 1):
        first = [
            cnf.names[
                (
                    "exceptional-template-class",
                    color,
                    TEMPLATE,
                    ordered_classes[0],
                    point,
                )
            ]
            for point in graph_points[color]
        ]
        second = [
            cnf.names[
                (
                    "exceptional-template-class",
                    color,
                    TEMPLATE,
                    ordered_classes[1],
                    point,
                )
            ]
            for point in graph_points[color]
        ]
        cnf.lexicographic_leq(
            first,
            second,
            ("template-class-order", color, *ordered_classes),
        )
    return cnf, {
        "case": CASE,
        "template": TEMPLATE,
        "ordered_classes": ordered_classes,
        "ordered_colors": (0, 1),
        "base_metadata": base_metadata,
    }


def render() -> str:
    cnf, metadata = build_instance()
    lines = [
        "c ERDOS617 local L=208 classified hard-branch quotient, version 1",
        (
            f"c case={metadata['case']} template={metadata['template']} "
            "independent_twin_class_orders=2"
        ),
        "c each class 4/5 swap is a template-representation automorphism",
        f"p cnf {cnf.variables} {len(cnf.clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in cnf.clauses)
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(render(), encoding="ascii", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

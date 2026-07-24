#!/usr/bin/env python3
"""Representation quotient for the undecided E014 45/44 branch."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_209_double_classified_cnf import (  # noqa: E402
    VARIABLE_45,
    build_instance as build_classified,
)

CASE = "balanced_double45_44"
TEMPLATE = "b4555_large_a2"
TEMPLATE_COLOR = 1
ORDERED_CLASSES = (4, 5)


def build_instance():
    cnf, base_metadata = build_classified(CASE, VARIABLE_45, TEMPLATE)
    graph_points = base_metadata["base_metadata"]["graph_points"][TEMPLATE_COLOR]
    first = [
        cnf.names[(
            "exceptional-template-class",
            TEMPLATE_COLOR,
            TEMPLATE,
            ORDERED_CLASSES[0],
            point,
        )]
        for point in graph_points
    ]
    second = [
        cnf.names[(
            "exceptional-template-class",
            TEMPLATE_COLOR,
            TEMPLATE,
            ORDERED_CLASSES[1],
            point,
        )]
        for point in graph_points
    ]
    cnf.lexicographic_leq(
        first,
        second,
        ("template-class-order", TEMPLATE_COLOR, *ORDERED_CLASSES),
    )
    return cnf, {
        "case": CASE,
        "variable_template": VARIABLE_45,
        "template": TEMPLATE,
        "template_color": TEMPLATE_COLOR,
        "ordered_classes": ORDERED_CLASSES,
        "base_metadata": base_metadata,
    }


def render() -> str:
    cnf, metadata = build_instance()
    lines = [
        "c ERDOS617 local L=209 classified hard-branch quotient, version 1",
        (
            f"c case={metadata['case']} template={metadata['template']} "
            f"template_color={metadata['template_color']} twin_class_orders=1"
        ),
        "c class 4/5 swap is a template-representation automorphism",
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

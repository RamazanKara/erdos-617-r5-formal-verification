#!/usr/bin/env python3
"""Full template-automorphism quotients for unresolved E014 50/39 branches."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.generate_local_209_double_classified_u50_canonical_cnf import (  # noqa: E402
    TEMPLATE_COLOR,
    TEMPLATES,
    build_instance as build_twin_canonical,
)

AUTOMORPHISMS = {
    "u4455_a1": ((0, 1, 2, 3), (2, 3, 0, 1)),
    "u4455_a2": ((0, 1, 2, 6), (1, 0, 6, 2)),
}


def build_instance(template: str):
    if template not in TEMPLATES:
        raise ValueError(f"unsupported order-19 template {template!r}")
    cnf, base_metadata = build_twin_canonical(template)
    classes, permuted_classes = AUTOMORPHISMS[template]
    graph_points = base_metadata["base_metadata"]["base_metadata"]["graph_points"]
    points = graph_points[TEMPLATE_COLOR]
    first = [
        cnf.names[(
            "exceptional-template-class",
            TEMPLATE_COLOR,
            template,
            class_index,
            point,
        )]
        for class_index in classes
        for point in points
    ]
    second = [
        cnf.names[(
            "exceptional-template-class",
            TEMPLATE_COLOR,
            template,
            class_index,
            point,
        )]
        for class_index in permuted_classes
        for point in points
    ]
    cnf.lexicographic_leq(
        first,
        second,
        ("template-coupled-class-order", TEMPLATE_COLOR, template),
    )
    return cnf, {
        "template": template,
        "template_color": TEMPLATE_COLOR,
        "classes": classes,
        "permuted_classes": permuted_classes,
        "base_metadata": base_metadata,
    }


def render(template: str) -> str:
    cnf, metadata = build_instance(template)
    lines = [
        "c ERDOS617 local L=209 classified 50/39 full canonical quotient, version 1",
        (
            f"c case=unbalanced_double50_39 template={template} "
            f"coupled_classes={','.join(map(str, metadata['classes']))}"
        ),
        "c twin and coupled class permutations are representation automorphisms",
        f"p cnf {cnf.variables} {len(cnf.clauses)}",
    ]
    lines.extend(" ".join(map(str, clause)) + " 0" for clause in cnf.clauses)
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--template", choices=TEMPLATES, required=True)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(render(args.template), encoding="ascii", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

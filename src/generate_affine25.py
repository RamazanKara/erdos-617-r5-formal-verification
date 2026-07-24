#!/usr/bin/env python3
"""Generate the standard AG(2,5) balanced coloring of K_25."""

from __future__ import annotations

import argparse
from pathlib import Path

FIELD_ORDER = 5


def point(vertex: int) -> tuple[int, int]:
    return divmod(vertex, FIELD_ORDER)


def edge_color(u: int, v: int) -> int:
    x1, y1 = point(u)
    x2, y2 = point(v)
    dx = (x2 - x1) % FIELD_ORDER
    dy = (y2 - y1) % FIELD_ORDER
    if dx == 0:
        return 4
    slope = (dy * pow(dx, -1, FIELD_ORDER)) % FIELD_ORDER
    return slope if slope < 4 else 4


def render() -> str:
    lines = ["ERDOS617-COLORING-V1 25 5 6"]
    for u in range(25):
        for v in range(u + 1, 25):
            lines.append(f"{u} {v} {edge_color(u, v)}")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(render(), encoding="ascii", newline="\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

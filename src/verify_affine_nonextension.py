#!/usr/bin/env python3
"""Check the finite premises of the two-orthogonal-partitions nonextension proof."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def read_matrix(path: Path) -> list[list[int]]:
    lines = path.read_text(encoding="ascii").splitlines()
    if lines[0] != "ERDOS617-COLORING-V1 25 5 6" or len(lines) != 301:
        raise ValueError("unexpected coloring scope or length")
    matrix = [[-1] * 25 for _ in range(25)]
    cursor = 1
    for u in range(25):
        for v in range(u + 1, 25):
            fields = tuple(map(int, lines[cursor].split()))
            if fields[:2] != (u, v) or not 0 <= fields[2] < 5:
                raise ValueError(f"bad edge line {cursor + 1}")
            matrix[u][v] = matrix[v][u] = fields[2]
            cursor += 1
    return matrix


def parallel_partition(slope: int) -> list[list[int]]:
    blocks: list[list[int]] = []
    for intercept in range(5):
        block = []
        for x in range(5):
            y = (slope * x + intercept) % 5
            block.append(5 * x + y)
        blocks.append(sorted(block))
    return blocks


def check_partition(matrix: list[list[int]], color: int) -> list[list[int]]:
    blocks = parallel_partition(color)
    assert sorted(vertex for block in blocks for vertex in block) == list(range(25))
    block_of = {}
    for index, block in enumerate(blocks):
        for vertex in block:
            block_of[vertex] = index
    for u in range(25):
        for v in range(u + 1, 25):
            same_block = block_of[u] == block_of[v]
            if (matrix[u][v] == color) != same_block:
                raise ValueError(
                    f"color {color} is not exactly the union of its five line cliques"
                )
    return blocks


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("coloring", type=Path)
    args = parser.parse_args()
    matrix = read_matrix(args.coloring)
    first = check_partition(matrix, 0)
    second = check_partition(matrix, 1)
    intersections = [[len(set(a) & set(b)) for b in second] for a in first]
    if intersections != [[1] * 5 for _ in range(5)]:
        raise ValueError("the two line partitions are not orthogonal")
    raw = args.coloring.read_bytes()
    result = {
        "claim": "AFFINE25-NONEXTENSION",
        "coloring_sha256": hashlib.sha256(raw).hexdigest(),
        "colors_used": [0, 1],
        "partition_block_sizes": [[len(b) for b in first], [len(b) for b in second]],
        "cross_intersection_sizes": intersections,
        "finite_premises_checked": True,
        "scope": "this exact labeled K25 coloring; no claim about other K25 colorings",
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

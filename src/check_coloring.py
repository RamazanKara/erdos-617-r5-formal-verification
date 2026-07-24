#!/usr/bin/env python3
"""Independent exhaustive semantic checker for ERDOS617-COLORING-V1 files."""

from __future__ import annotations

import argparse
import hashlib
import itertools
import sys
from pathlib import Path

MAGIC = "ERDOS617-COLORING-V1"


class FormatError(ValueError):
    pass


def parse_coloring(path: Path) -> tuple[int, int, int, list[list[int]], str]:
    raw = path.read_bytes()
    try:
        text = raw.decode("ascii")
    except UnicodeDecodeError as exc:
        raise FormatError("file is not ASCII") from exc
    lines = text.splitlines()
    if not lines:
        raise FormatError("empty file")
    header = lines[0].split()
    if len(header) != 4 or header[0] != MAGIC:
        raise FormatError(f"expected '{MAGIC} n r k' header")
    try:
        n, r, k = map(int, header[1:])
    except ValueError as exc:
        raise FormatError("header parameters must be decimal integers") from exc
    if not (2 <= n <= 64 and 1 <= r < 64 and 2 <= k <= n):
        raise FormatError("unsupported header parameters")

    expected_edges = n * (n - 1) // 2
    if len(lines) != expected_edges + 1:
        raise FormatError(
            f"expected {expected_edges} edge lines, found {len(lines) - 1}"
        )
    colors = [[-1] * n for _ in range(n)]
    line_index = 1
    for expected_u in range(n):
        for expected_v in range(expected_u + 1, n):
            fields = lines[line_index].split()
            if len(fields) != 3:
                raise FormatError(f"line {line_index + 1}: expected three integers")
            try:
                u, v, color = map(int, fields)
            except ValueError as exc:
                raise FormatError(
                    f"line {line_index + 1}: non-integer edge field"
                ) from exc
            if (u, v) != (expected_u, expected_v):
                raise FormatError(
                    f"line {line_index + 1}: expected edge "
                    f"{expected_u} {expected_v}, found {u} {v}"
                )
            if not 0 <= color < r:
                raise FormatError(f"line {line_index + 1}: color outside [0,{r})")
            colors[u][v] = colors[v][u] = color
            line_index += 1
    digest = hashlib.sha256(raw).hexdigest()
    return n, r, k, colors, digest


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("path", type=Path)
    parser.add_argument("--expect-n", type=int, required=True)
    parser.add_argument("--expect-r", type=int, required=True)
    parser.add_argument("--expect-k", type=int, required=True)
    args = parser.parse_args()

    try:
        n, r, k, colors, digest = parse_coloring(args.path)
    except (OSError, FormatError) as exc:
        print(f"MALFORMED: {exc}", file=sys.stderr)
        return 2
    expected = (args.expect_n, args.expect_r, args.expect_k)
    if (n, r, k) != expected:
        print(
            f"MALFORMED: scope {(n, r, k)} does not match required {expected}",
            file=sys.stderr,
        )
        return 2

    all_colors = (1 << r) - 1
    subsets_checked = 0
    for subset in itertools.combinations(range(n), k):
        seen = 0
        for u, v in itertools.combinations(subset, 2):
            seen |= 1 << colors[u][v]
        subsets_checked += 1
        if seen != all_colors:
            missing = [c for c in range(r) if not (seen >> c) & 1]
            print(
                f"INVALID subset={' '.join(map(str, subset))} "
                f"missing={','.join(map(str, missing))}"
            )
            return 1

    print(
        f"VALID n={n} r={r} k={k} edges={n * (n - 1) // 2} "
        f"subsets={subsets_checked} sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

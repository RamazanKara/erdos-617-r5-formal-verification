#!/usr/bin/env python3
"""Check semantic clause-multiset inclusion between two strict DIMACS files."""

from __future__ import annotations

import argparse
import hashlib
from collections import Counter
from pathlib import Path


class DimacsError(ValueError):
    pass


def parse(path: Path) -> tuple[int, Counter[tuple[int, ...]], str]:
    raw = path.read_bytes()
    variables: int | None = None
    declared: int | None = None
    clauses: Counter[tuple[int, ...]] = Counter()
    for line_number, raw_line in enumerate(raw.splitlines(), start=1):
        try:
            fields = raw_line.decode("ascii").split()
        except UnicodeDecodeError as exc:
            raise DimacsError(f"non-ASCII input on line {line_number}") from exc
        if not fields or fields[0] == "c":
            continue
        if fields[0] == "p":
            if variables is not None or len(fields) != 4 or fields[1] != "cnf":
                raise DimacsError(f"bad header on line {line_number}")
            try:
                variables, declared = map(int, fields[2:])
            except ValueError as exc:
                raise DimacsError(f"bad header integer on line {line_number}") from exc
            if variables < 0 or declared < 0:
                raise DimacsError("negative DIMACS dimension")
            continue
        if variables is None or fields[-1] != "0" or "0" in fields[:-1]:
            raise DimacsError(f"clause before header or malformed zero on line {line_number}")
        try:
            literals = tuple(map(int, fields[:-1]))
        except ValueError as exc:
            raise DimacsError(f"bad literal on line {line_number}") from exc
        if any(abs(literal) > variables for literal in literals):
            raise DimacsError(f"literal outside range on line {line_number}")
        if len(set(literals)) != len(literals) or any(
            -literal in literals for literal in literals
        ):
            raise DimacsError(f"duplicate or tautological clause on line {line_number}")
        clauses[tuple(sorted(literals))] += 1
    if variables is None or declared != sum(clauses.values()):
        raise DimacsError("DIMACS clause count mismatch")
    return variables, clauses, hashlib.sha256(raw).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("superset", type=Path)
    parser.add_argument("subset", type=Path)
    args = parser.parse_args()

    try:
        superset_variables, superset, superset_hash = parse(args.superset)
        subset_variables, subset, subset_hash = parse(args.subset)
        if subset_variables != superset_variables:
            raise DimacsError("variable bounds differ")
        missing = subset - superset
        if missing:
            clause, multiplicity = next(iter(missing.items()))
            raise DimacsError(
                f"subset clause absent {multiplicity} time(s): {clause!r}"
            )
    except (OSError, DimacsError) as exc:
        print(f"CNF-SUBSET-INVALID: {exc}")
        return 1

    print(
        "CNF-SUBSET-VALID "
        f"superset_clauses={sum(superset.values())} "
        f"subset_clauses={sum(subset.values())} "
        f"superset_sha256={superset_hash} subset_sha256={subset_hash}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

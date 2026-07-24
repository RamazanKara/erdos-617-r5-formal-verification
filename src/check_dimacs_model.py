#!/usr/bin/env python3
"""Independently check a complete SAT model against an exact DIMACS CNF."""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path


def read_cnf(path: Path) -> tuple[int, list[tuple[int, ...]]]:
    variables = None
    declared_clauses = None
    clauses: list[tuple[int, ...]] = []
    pending: list[int] = []
    with path.open("r", encoding="ascii") as stream:
        for line_number, line in enumerate(stream, start=1):
            stripped = line.strip()
            if not stripped or stripped.startswith("c"):
                continue
            if stripped.startswith("p"):
                fields = stripped.split()
                if variables is not None or len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                    raise ValueError(f"{path}:{line_number}: invalid DIMACS header")
                variables = int(fields[2])
                declared_clauses = int(fields[3])
                if variables < 0 or declared_clauses < 0:
                    raise ValueError(f"{path}:{line_number}: negative DIMACS dimension")
                continue
            if variables is None:
                raise ValueError(f"{path}:{line_number}: clause before header")
            for field in stripped.split():
                literal = int(field)
                if literal == 0:
                    clauses.append(tuple(pending))
                    pending.clear()
                else:
                    if abs(literal) > variables:
                        raise ValueError(
                            f"{path}:{line_number}: literal {literal} exceeds header"
                        )
                    pending.append(literal)
    if variables is None or declared_clauses is None:
        raise ValueError(f"{path}: missing DIMACS header")
    if pending:
        raise ValueError(f"{path}: unterminated DIMACS clause")
    if len(clauses) != declared_clauses:
        raise ValueError(
            f"{path}: header declares {declared_clauses} clauses, read {len(clauses)}"
        )
    return variables, clauses


def read_model(path: Path, variables: int) -> tuple[bool, ...]:
    saw_sat = False
    assignment: dict[int, bool] = {}
    with path.open("r", encoding="ascii", errors="strict") as stream:
        for line_number, line in enumerate(stream, start=1):
            stripped = line.strip()
            if not stripped or stripped.startswith("c"):
                continue
            if stripped.startswith("s"):
                if stripped != "s SATISFIABLE":
                    raise ValueError(f"{path}:{line_number}: status is not SATISFIABLE")
                saw_sat = True
                continue
            if not stripped.startswith("v"):
                continue
            for field in stripped.split()[1:]:
                literal = int(field)
                if literal == 0:
                    continue
                variable = abs(literal)
                if variable < 1 or variable > variables:
                    raise ValueError(
                        f"{path}:{line_number}: model literal {literal} out of range"
                    )
                value = literal > 0
                if variable in assignment and assignment[variable] != value:
                    raise ValueError(
                        f"{path}:{line_number}: conflicting value for variable {variable}"
                    )
                assignment[variable] = value
    if not saw_sat:
        raise ValueError(f"{path}: missing SATISFIABLE status")
    missing = [variable for variable in range(1, variables + 1) if variable not in assignment]
    if missing:
        raise ValueError(
            f"{path}: incomplete model; first missing variable is {missing[0]}"
        )
    return tuple(assignment[variable] for variable in range(1, variables + 1))


def check_model(clauses: list[tuple[int, ...]], assignment: tuple[bool, ...]) -> None:
    for index, clause in enumerate(clauses, start=1):
        if not any(
            assignment[abs(literal) - 1] == (literal > 0)
            for literal in clause
        ):
            raise ValueError(f"model falsifies DIMACS clause {index}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("cnf", type=Path)
    parser.add_argument("model", type=Path)
    args = parser.parse_args()
    variables, clauses = read_cnf(args.cnf)
    assignment = read_model(args.model, variables)
    check_model(clauses, assignment)
    encoded = bytes(value for value in assignment)
    print(
        f"DIMACS-MODEL-VALID variables={variables} clauses={len(clauses)} "
        f"assignment_sha256={hashlib.sha256(encoded).hexdigest()}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

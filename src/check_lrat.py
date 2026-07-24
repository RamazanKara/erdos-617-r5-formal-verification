#!/usr/bin/env python3
"""Small independent checker for RUP-only ASCII LRAT certificates.

RAT steps (negative hint identifiers) are deliberately rejected.  Proof input
is streamed so the large E006 certificate can be checked with bounded memory.
"""

from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path


class CheckError(ValueError):
    pass


def parse_cnf(path: Path) -> tuple[int, dict[int, tuple[int, ...]], str]:
    raw = path.read_bytes()
    lines = raw.decode("ascii").splitlines()
    variables = None
    declared_clauses = None
    clauses: dict[int, tuple[int, ...]] = {}
    for line_number, line in enumerate(lines, start=1):
        fields = line.split()
        if not fields or fields[0] == "c":
            continue
        if fields[0] == "p":
            if variables is not None or len(fields) != 4 or fields[1] != "cnf":
                raise CheckError(f"bad DIMACS header on line {line_number}")
            variables, declared_clauses = map(int, fields[2:])
            continue
        if variables is None or fields[-1] != "0":
            raise CheckError(f"clause before header or missing zero on line {line_number}")
        literals = tuple(map(int, fields[:-1]))
        if any(literal == 0 or abs(literal) > variables for literal in literals):
            raise CheckError(f"literal outside range on line {line_number}")
        if len(set(literals)) != len(literals) or any(-literal in literals for literal in literals):
            raise CheckError(f"duplicate or tautological clause on line {line_number}")
        clauses[len(clauses) + 1] = literals
    if variables is None or declared_clauses != len(clauses):
        raise CheckError("DIMACS clause count mismatch")
    return variables, clauses, hashlib.sha256(raw).hexdigest()


def literal_value(literal: int, assignment: list[int]) -> int:
    value = assignment[abs(literal)]
    if value == 0:
        return 0
    return value if literal > 0 else -value


def check_rup(
    new_clause: tuple[int, ...],
    hints: list[int],
    clauses: dict[int, tuple[int, ...]],
    variables: int,
) -> None:
    assignment = [0] * (variables + 1)
    for literal in new_clause:
        variable = abs(literal)
        required = -1 if literal > 0 else 1
        if assignment[variable] not in (0, required):
            raise CheckError("tautological new clause")
        assignment[variable] = required

    conflict = False
    for position, hint in enumerate(hints):
        if hint <= 0:
            raise CheckError("RAT or nonpositive hint in RUP-only proof")
        clause = clauses.get(hint)
        if clause is None:
            raise CheckError(f"hint references absent clause {hint}")
        unassigned = 0
        unit_literal = 0
        satisfied = False
        for literal in clause:
            value = literal_value(literal, assignment)
            if value > 0:
                satisfied = True
                break
            if value == 0:
                unassigned += 1
                unit_literal = literal
        if satisfied or unassigned > 1:
            raise CheckError(f"hint {hint} is neither unit nor conflicting")
        if unassigned == 0:
            if position != len(hints) - 1:
                raise CheckError("conflict hint is not last")
            conflict = True
            break
        variable = abs(unit_literal)
        required = 1 if unit_literal > 0 else -1
        if assignment[variable] not in (0, required):
            raise CheckError("inconsistent unit assignment without explicit conflict")
        assignment[variable] = required
    if not conflict:
        raise CheckError("RUP hints do not end in a conflict")


def check_lrat(cnf_path: Path, proof_path: Path) -> tuple[int, int, str]:
    variables, clauses, cnf_digest = parse_cnf(cnf_path)
    original_count = len(clauses)
    # An LRAT deletion command is labelled by the most recent addition index;
    # it does not introduce a fresh clause identifier.  The converter emits an
    # initial deletion labelled by the final original-CNF index.
    last_addition_identifier = original_count
    additions = 0
    empty_derived = False
    proof_digest = hashlib.sha256()
    with proof_path.open("rb") as proof_stream:
        proof_lines = enumerate(proof_stream, start=1)
        for line_number, raw_line in proof_lines:
            proof_digest.update(raw_line)
            fields = raw_line.decode("ascii").split()
            # Match the historical checker semantics: the first derived empty
            # clause completes the proof.  Continue reading solely so the
            # reported digest covers every byte and non-ASCII suffixes are
            # still rejected, without retaining a potentially huge proof.
            if empty_derived:
                continue
            if not fields or fields[0] == "c":
                continue
            try:
                identifier = int(fields[0])
            except ValueError as exc:
                raise CheckError(f"bad identifier on LRAT line {line_number}") from exc
            if len(fields) >= 2 and fields[1] == "d":
                if identifier != last_addition_identifier:
                    raise CheckError(f"mislabelled deletion on line {line_number}")
                if fields[-1] != "0":
                    raise CheckError(f"unterminated deletion on line {line_number}")
                for token in fields[2:-1]:
                    deleted = int(token)
                    if deleted not in clauses:
                        raise CheckError(f"deleting absent clause {deleted}")
                    del clauses[deleted]
                continue

            if identifier <= last_addition_identifier:
                raise CheckError(f"nonincreasing addition identifier on line {line_number}")
            last_addition_identifier = identifier

            try:
                first_zero = fields.index("0", 1)
                second_zero = fields.index("0", first_zero + 1)
            except ValueError as exc:
                raise CheckError(f"malformed addition on line {line_number}") from exc
            if second_zero != len(fields) - 1:
                raise CheckError(f"trailing LRAT tokens on line {line_number}")
            clause = tuple(map(int, fields[1:first_zero]))
            hints = list(map(int, fields[first_zero + 1 : second_zero]))
            if any(literal == 0 or abs(literal) > variables for literal in clause):
                raise CheckError(f"new literal outside range on line {line_number}")
            if len(set(clause)) != len(clause) or any(-literal in clause for literal in clause):
                raise CheckError(f"duplicate or tautological addition on line {line_number}")
            check_rup(clause, hints, clauses, variables)
            clauses[identifier] = clause
            additions += 1
            if not clause:
                empty_derived = True
    if not empty_derived:
        raise CheckError("LRAT proof did not derive the empty clause")
    combined = hashlib.sha256(
        (cnf_digest + proof_digest.hexdigest()).encode("ascii")
    ).hexdigest()
    return original_count, additions, combined


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("cnf", type=Path)
    parser.add_argument("proof", type=Path)
    args = parser.parse_args()
    try:
        clauses, additions, combined = check_lrat(args.cnf, args.proof)
    except (OSError, UnicodeDecodeError, CheckError) as exc:
        print(f"LRAT-INVALID: {exc}", file=sys.stderr)
        return 1
    print(
        f"LRAT-VALID original_clauses={clauses} additions={additions} "
        f"combined_sha256={combined}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

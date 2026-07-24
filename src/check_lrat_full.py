#!/usr/bin/env python3
"""Independent streaming checker for ASCII LRAT, including RAT additions."""

from __future__ import annotations

import argparse
import hashlib
import sys
from pathlib import Path


class CheckError(ValueError):
    pass


def parse_cnf(path: Path) -> tuple[int, dict[int, tuple[int, ...]], str]:
    raw = path.read_bytes()
    variables: int | None = None
    declared: int | None = None
    clauses: dict[int, tuple[int, ...]] = {}
    for line_number, raw_line in enumerate(raw.splitlines(), start=1):
        fields = raw_line.decode("ascii").split()
        if not fields or fields[0] == "c":
            continue
        if fields[0] == "p":
            if variables is not None or len(fields) != 4 or fields[1] != "cnf":
                raise CheckError(f"bad DIMACS header on line {line_number}")
            variables, declared = map(int, fields[2:])
            if variables < 0 or declared < 0:
                raise CheckError("negative DIMACS dimension")
            continue
        if variables is None or fields[-1] != "0" or "0" in fields[:-1]:
            raise CheckError(f"malformed DIMACS clause on line {line_number}")
        clause = tuple(map(int, fields[:-1]))
        if any(abs(literal) > variables for literal in clause):
            raise CheckError(f"literal outside range on line {line_number}")
        if len(set(clause)) != len(clause) or any(-literal in clause for literal in clause):
            raise CheckError(f"noncanonical DIMACS clause on line {line_number}")
        clauses[len(clauses) + 1] = clause
    if variables is None or declared != len(clauses):
        raise CheckError("DIMACS clause count mismatch")
    return variables, clauses, hashlib.sha256(raw).hexdigest()


def literal_value(literal: int, assignment: list[int]) -> int:
    value = assignment[abs(literal)]
    return value if literal > 0 else -value


def falsifying_assignment(
    literals: tuple[int, ...],
    variables: int,
    seed: list[int] | None = None,
) -> list[int] | None:
    assignment = [0] * (variables + 1) if seed is None else seed.copy()
    for literal in literals:
        variable = abs(literal)
        required = -1 if literal > 0 else 1
        if assignment[variable] == -required:
            return None
        assignment[variable] = required
    return assignment


def check_chain(
    falsified_clause: tuple[int, ...],
    hints: list[int],
    clauses: dict[int, tuple[int, ...]],
    variables: int,
    seed: list[int] | None = None,
) -> tuple[bool, list[int] | None]:
    """Run a named unit chain and return its conflict flag and assignment.

    A tautological resolvent is represented by ``falsifying_assignment``
    returning ``None`` and is accepted without consulting its optional hints.
    """

    assignment = falsifying_assignment(falsified_clause, variables, seed)
    if assignment is None:
        return True, None
    conflict = False
    for position, hint in enumerate(hints):
        if hint <= 0:
            raise CheckError("nonpositive identifier inside a propagation chain")
        clause = clauses.get(hint)
        if clause is None:
            raise CheckError(f"hint references absent clause {hint}")
        unit_literal = 0
        unassigned = 0
        satisfied = False
        for literal in clause:
            value = literal_value(literal, assignment)
            if value > 0:
                satisfied = True
                break
            if value == 0:
                unit_literal = literal
                unassigned += 1
        if satisfied or unassigned > 1:
            raise CheckError(f"hint {hint} is neither unit nor conflicting")
        if unassigned == 0:
            if position != len(hints) - 1:
                raise CheckError("conflict hint is not last in its chain")
            conflict = True
            break
        variable = abs(unit_literal)
        required = 1 if unit_literal > 0 else -1
        if assignment[variable] not in (0, required):
            raise CheckError("inconsistent unit without an explicit conflict")
        assignment[variable] = required
    return conflict, assignment


def check_addition(
    clause: tuple[int, ...],
    hints: list[int],
    clauses: dict[int, tuple[int, ...]],
    occurrences: dict[int, set[int]],
    variables: int,
) -> bool:
    """Check one LRAT addition and return whether it used RAT."""

    first_rat = next((index for index, hint in enumerate(hints) if hint < 0), len(hints))
    prefix = hints[:first_rat]
    if any(hint <= 0 for hint in prefix):
        raise CheckError("bad initial propagation hint")
    prefix_conflict, common_assignment = check_chain(
        clause, prefix, clauses, variables
    )
    if prefix_conflict:
        return False
    if first_rat == len(hints):
        raise CheckError("RUP hints do not end in conflict")
    if not clause:
        raise CheckError("empty clause cannot be justified by RAT")

    groups: list[tuple[int, list[int]]] = []
    cursor = first_rat
    while cursor < len(hints):
        marker = hints[cursor]
        if marker >= 0:
            raise CheckError("RAT group does not start with a negative clause id")
        clause_id = -marker
        cursor += 1
        start = cursor
        while cursor < len(hints) and hints[cursor] > 0:
            cursor += 1
        groups.append((clause_id, hints[start:cursor]))

    pivot = clause[0]
    expected = sorted(occurrences.get(-pivot, set()))
    observed = [clause_id for clause_id, _ in groups]
    if observed != expected:
        raise CheckError(
            "RAT groups do not exhaust active clauses containing the opposite pivot"
        )
    for clause_id, chain in groups:
        opposite = clauses.get(clause_id)
        if opposite is None or -pivot not in opposite:
            raise CheckError(f"bad RAT resolvent clause {clause_id}")
        resolvent_extension = tuple(
            literal for literal in opposite if literal != -pivot
        )
        resolvent_conflict, _ = check_chain(
            resolvent_extension,
            chain,
            clauses,
            variables,
            common_assignment,
        )
        if not resolvent_conflict:
            raise CheckError(f"RAT resolvent {clause_id} does not end in conflict")
    return True


def add_occurrences(
    identifier: int,
    clause: tuple[int, ...],
    occurrences: dict[int, set[int]],
) -> None:
    for literal in clause:
        occurrences.setdefault(literal, set()).add(identifier)


def remove_occurrences(
    identifier: int,
    clause: tuple[int, ...],
    occurrences: dict[int, set[int]],
) -> None:
    for literal in clause:
        identifiers = occurrences[literal]
        identifiers.remove(identifier)
        if not identifiers:
            del occurrences[literal]


def check_lrat(path_cnf: Path, path_proof: Path) -> tuple[int, int, int, str]:
    variables, clauses, cnf_digest = parse_cnf(path_cnf)
    proof_variable_bound = variables
    original_count = len(clauses)
    occurrences: dict[int, set[int]] = {}
    for identifier, clause in clauses.items():
        add_occurrences(identifier, clause, occurrences)
    last_addition = original_count
    additions = 0
    rat_additions = 0
    empty_derived = False
    proof_digest = hashlib.sha256()
    with path_proof.open("rb") as stream:
        for line_number, raw_line in enumerate(stream, start=1):
            proof_digest.update(raw_line)
            fields = raw_line.decode("ascii").split()
            if empty_derived:
                continue
            if not fields or fields[0] == "c":
                continue
            try:
                identifier = int(fields[0])
            except ValueError as exc:
                raise CheckError(f"bad identifier on LRAT line {line_number}") from exc
            if len(fields) >= 2 and fields[1] == "d":
                if identifier != last_addition or fields[-1] != "0":
                    raise CheckError(f"malformed deletion on line {line_number}")
                for token in fields[2:-1]:
                    deleted = int(token)
                    clause = clauses.pop(deleted, None)
                    if clause is None:
                        raise CheckError(f"deleting absent clause {deleted}")
                    remove_occurrences(deleted, clause, occurrences)
                continue
            if identifier <= last_addition:
                raise CheckError(f"nonincreasing addition identifier on line {line_number}")
            last_addition = identifier
            try:
                first_zero = fields.index("0", 1)
                second_zero = fields.index("0", first_zero + 1)
            except ValueError as exc:
                raise CheckError(f"malformed addition on line {line_number}") from exc
            if second_zero != len(fields) - 1:
                raise CheckError(f"trailing LRAT tokens on line {line_number}")
            clause = tuple(map(int, fields[1:first_zero]))
            hints = list(map(int, fields[first_zero + 1 : second_zero]))
            if any(literal == 0 for literal in clause):
                raise CheckError(f"zero literal in addition on line {line_number}")
            if len(set(clause)) != len(clause) or any(-literal in clause for literal in clause):
                raise CheckError(f"noncanonical addition on line {line_number}")
            if clause:
                proof_variable_bound = max(
                    proof_variable_bound, max(abs(literal) for literal in clause)
                )
            if check_addition(
                clause,
                hints,
                clauses,
                occurrences,
                proof_variable_bound,
            ):
                rat_additions += 1
            clauses[identifier] = clause
            add_occurrences(identifier, clause, occurrences)
            additions += 1
            if not clause:
                empty_derived = True
    if not empty_derived:
        raise CheckError("LRAT proof did not derive the empty clause")
    combined = hashlib.sha256(
        (cnf_digest + proof_digest.hexdigest()).encode("ascii")
    ).hexdigest()
    return original_count, additions, rat_additions, combined


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("cnf", type=Path)
    parser.add_argument("proof", type=Path)
    args = parser.parse_args()
    try:
        originals, additions, rat_additions, combined = check_lrat(
            args.cnf, args.proof
        )
    except (OSError, UnicodeDecodeError, CheckError) as error:
        print(f"LRAT-INVALID: {error}", file=sys.stderr)
        return 1
    print(
        f"LRAT-VALID original_clauses={originals} additions={additions} "
        f"rat_additions={rat_additions} combined_sha256={combined}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

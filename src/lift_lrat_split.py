#!/usr/bin/env python3
"""Lift two unit-branch RUP LRAT refutations over their exact base CNF.

``write_split_drup`` emits a candidate DRUP trace for global reconversion.
``write_split_lrat`` instead preserves and remaps RUP hints directly.  Either
output remains a proof-producer result and must be checked independently
against the unsplit base CNF before it can carry a theorem claim.
"""

from __future__ import annotations

import argparse
from pathlib import Path


class LiftError(ValueError):
    pass


def parse_cnf(path: Path) -> tuple[int, list[tuple[int, ...]]]:
    variables = None
    declared = None
    clauses: list[tuple[int, ...]] = []
    for line_number, raw_line in enumerate(path.read_bytes().splitlines(), start=1):
        fields = raw_line.split()
        if not fields or fields[0] == b"c":
            continue
        if fields[0] == b"p":
            if variables is not None or len(fields) != 4 or fields[1] != b"cnf":
                raise LiftError(f"bad DIMACS header on line {line_number}")
            variables, declared = map(int, fields[2:])
            continue
        if variables is None or fields[-1] != b"0":
            raise LiftError(f"bad DIMACS clause on line {line_number}")
        clause = tuple(map(int, fields[:-1]))
        if any(literal == 0 or abs(literal) > variables for literal in clause):
            raise LiftError(f"literal outside range on line {line_number}")
        if len(set(clause)) != len(clause) or any(-literal in clause for literal in clause):
            raise LiftError(f"noncanonical clause on line {line_number}")
        clauses.append(clause)
    if variables is None or declared != len(clauses):
        raise LiftError("DIMACS clause count mismatch")
    return variables, clauses


def audit_unit_extension(base: Path, branch: Path, literal: int) -> int:
    base_variables, base_clauses = parse_cnf(base)
    branch_variables, branch_clauses = parse_cnf(branch)
    if branch_variables != base_variables:
        raise LiftError("unit branch changes the base variable bound")
    if branch_clauses != [*base_clauses, (literal,)]:
        raise LiftError("unit branch is not the exact base plus its named unit")
    return len(branch_clauses)


def write_lifted_branch(
    proof: Path,
    output,
    *,
    branch_originals: int,
    assumption: int,
) -> int:
    """Stream one branch's conditional DRUP additions to ``output``."""

    empty_seen = False
    last_identifier = branch_originals
    additions = 0
    last_written: tuple[int, ...] | None = None
    with proof.open("rb") as proof_stream:
        for line_number, raw_line in enumerate(proof_stream, start=1):
            fields = raw_line.split()
            if not fields or fields[0] == b"c":
                continue
            try:
                identifier = int(fields[0])
            except ValueError as exc:
                raise LiftError(f"bad LRAT identifier on line {line_number}") from exc
            if len(fields) >= 2 and fields[1] == b"d":
                if identifier != last_identifier:
                    raise LiftError(f"mislabelled LRAT deletion on line {line_number}")
                if fields[-1] != b"0":
                    raise LiftError(f"unterminated LRAT deletion on line {line_number}")
                continue
            if identifier <= last_identifier:
                raise LiftError(f"nonincreasing LRAT identifier on line {line_number}")
            last_identifier = identifier
            try:
                first_zero = fields.index(b"0", 1)
                second_zero = fields.index(b"0", first_zero + 1)
            except ValueError as exc:
                raise LiftError(f"malformed LRAT addition on line {line_number}") from exc
            if second_zero != len(fields) - 1:
                raise LiftError(f"trailing LRAT tokens on line {line_number}")
            clause = tuple(map(int, fields[1:first_zero]))
            if len(set(clause)) != len(clause) or any(
                -literal in clause for literal in clause
            ):
                raise LiftError(f"noncanonical LRAT clause on line {line_number}")

            # C derived from F + assumption gives C v -assumption from F.  If
            # C contains the assumption, the lift is tautological and useless.
            if assumption not in clause:
                conditional = clause
                if -assumption not in conditional:
                    conditional = (*conditional, -assumption)
                output.write(
                    (" ".join(map(str, conditional)) + " 0\n").encode("ascii")
                )
                additions += 1
                last_written = conditional
            if not clause:
                empty_seen = True
                break
    if not empty_seen:
        raise LiftError("branch LRAT does not derive the empty clause")
    if last_written != (-assumption,):
        raise LiftError("branch lift does not finish with the opposite unit")
    return additions


def write_lifted_lrat_branch(
    proof: Path,
    output,
    *,
    branch_originals: int,
    assumption: int,
    next_identifier: int,
) -> tuple[int, int, int]:
    """Lift one RUP-only branch LRAT while preserving and remapping its hints."""

    empty_seen = False
    last_identifier = branch_originals
    additions = 0
    opposite_unit_identifier: int | None = None
    mapped: dict[int, int | None] = {}
    active_new: set[int] = set()
    with proof.open("rb") as proof_stream:
        for line_number, raw_line in enumerate(proof_stream, start=1):
            fields = raw_line.split()
            if not fields or fields[0] == b"c":
                continue
            try:
                identifier = int(fields[0])
            except ValueError as exc:
                raise LiftError(f"bad LRAT identifier on line {line_number}") from exc
            if len(fields) >= 2 and fields[1] == b"d":
                if identifier != last_identifier:
                    raise LiftError(f"mislabelled LRAT deletion on line {line_number}")
                if fields[-1] != b"0":
                    raise LiftError(f"unterminated LRAT deletion on line {line_number}")
                deleted_new: list[int] = []
                for token in fields[2:-1]:
                    deleted = int(token)
                    if deleted <= branch_originals:
                        # Keep all parent originals and omit the branch unit.
                        continue
                    if deleted not in mapped:
                        raise LiftError(
                            f"deletion {deleted} precedes its addition on line {line_number}"
                        )
                    remapped = mapped[deleted]
                    if remapped is not None and remapped in active_new:
                        active_new.remove(remapped)
                        deleted_new.append(remapped)
                if deleted_new:
                    output.write(
                        (
                            f"{next_identifier} d "
                            + " ".join(map(str, deleted_new))
                            + " 0\n"
                        ).encode("ascii")
                    )
                continue
            if identifier <= last_identifier:
                raise LiftError(f"nonincreasing LRAT identifier on line {line_number}")
            last_identifier = identifier
            try:
                first_zero = fields.index(b"0", 1)
                second_zero = fields.index(b"0", first_zero + 1)
            except ValueError as exc:
                raise LiftError(f"malformed LRAT addition on line {line_number}") from exc
            if second_zero != len(fields) - 1:
                raise LiftError(f"trailing LRAT tokens on line {line_number}")
            clause = tuple(map(int, fields[1:first_zero]))
            hints = tuple(map(int, fields[first_zero + 1 : second_zero]))
            if any(hint <= 0 for hint in hints):
                raise LiftError("direct LRAT lift requires a RUP-only branch proof")
            if len(set(clause)) != len(clause) or any(
                -literal in clause for literal in clause
            ):
                raise LiftError(f"noncanonical LRAT clause on line {line_number}")

            # C derived from F + assumption lifts to C v -assumption from F.
            # A clause already containing assumption lifts tautologically and
            # is omitted.  Its identifier is retained as an explicit skipped
            # mapping so later hints can discard it deterministically.
            if assumption in clause:
                mapped[identifier] = None
                continue
            conditional = clause
            if -assumption not in conditional:
                conditional = (*conditional, -assumption)

            remapped_hints: list[int] = []
            for hint in hints:
                if hint < branch_originals:
                    remapped_hints.append(hint)
                elif hint == branch_originals:
                    # The branch unit is already one of the assumptions made
                    # while checking the lifted clause.
                    continue
                else:
                    if hint not in mapped:
                        raise LiftError(
                            f"hint {hint} precedes its addition on line {line_number}"
                        )
                    remapped = mapped[hint]
                    if remapped is not None:
                        remapped_hints.append(remapped)

            next_identifier += 1
            mapped[identifier] = next_identifier
            active_new.add(next_identifier)
            fields_out = [
                str(next_identifier),
                *map(str, conditional),
                "0",
                *map(str, remapped_hints),
                "0",
            ]
            output.write((" ".join(fields_out) + "\n").encode("ascii"))
            additions += 1
            if not clause:
                empty_seen = True
                opposite_unit_identifier = next_identifier
                break
    if not empty_seen or opposite_unit_identifier is None:
        raise LiftError("branch LRAT does not derive the empty clause")
    # Nothing except the derived opposite unit can be referenced by the next
    # independent branch.  Explicit cleanup keeps checker memory bounded when
    # compositions are nested repeatedly.
    cleanup = sorted(active_new - {opposite_unit_identifier})
    for start in range(0, len(cleanup), 100_000):
        chunk = cleanup[start : start + 100_000]
        output.write(
            (
                f"{next_identifier} d "
                + " ".join(map(str, chunk))
                + " 0\n"
            ).encode("ascii")
        )
    return additions, next_identifier, opposite_unit_identifier


def write_split_lrat(
    base: Path,
    positive_cnf: Path,
    positive_lrat: Path,
    negative_cnf: Path,
    negative_lrat: Path,
    variable: int,
    output: Path,
) -> tuple[int, int]:
    """Compose two RUP-only unit-branch LRATs directly over the base CNF."""

    base_variables, base_clauses = parse_cnf(base)
    if variable <= 0 or variable > base_variables:
        raise LiftError("split variable is outside the base DIMACS range")
    positive_originals = audit_unit_extension(base, positive_cnf, variable)
    negative_originals = audit_unit_extension(base, negative_cnf, -variable)
    with output.open("wb") as stream:
        positive, next_identifier, negative_unit = write_lifted_lrat_branch(
            positive_lrat,
            stream,
            branch_originals=positive_originals,
            assumption=variable,
            next_identifier=len(base_clauses),
        )
        negative, next_identifier, positive_unit = write_lifted_lrat_branch(
            negative_lrat,
            stream,
            branch_originals=negative_originals,
            assumption=-variable,
            next_identifier=next_identifier,
        )
        stream.write(
            f"{next_identifier + 1} 0 {negative_unit} {positive_unit} 0\n".encode(
                "ascii"
            )
        )
    return positive, negative


def write_split_drup(
    base: Path,
    positive_cnf: Path,
    positive_lrat: Path,
    negative_cnf: Path,
    negative_lrat: Path,
    variable: int,
    output: Path,
) -> tuple[int, int]:
    base_variables, _ = parse_cnf(base)
    if variable <= 0 or variable > base_variables:
        raise LiftError("split variable is outside the base DIMACS range")
    positive_originals = audit_unit_extension(base, positive_cnf, variable)
    negative_originals = audit_unit_extension(base, negative_cnf, -variable)
    with output.open("wb") as stream:
        positive = write_lifted_branch(
            positive_lrat,
            stream,
            branch_originals=positive_originals,
            assumption=variable,
        )
        negative = write_lifted_branch(
            negative_lrat,
            stream,
            branch_originals=negative_originals,
            assumption=-variable,
        )
        stream.write(b"0\n")
    return positive, negative


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--positive-cnf", type=Path, required=True)
    parser.add_argument("--positive-lrat", type=Path, required=True)
    parser.add_argument("--negative-cnf", type=Path, required=True)
    parser.add_argument("--negative-lrat", type=Path, required=True)
    parser.add_argument("--variable", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    try:
        positive, negative = write_split_drup(
            args.base,
            args.positive_cnf,
            args.positive_lrat,
            args.negative_cnf,
            args.negative_lrat,
            args.variable,
            args.output,
        )
    except (OSError, UnicodeDecodeError, LiftError) as error:
        raise SystemExit(f"LRAT-SPLIT-LIFT-FAILED: {error}") from error
    print(
        f"LRAT-SPLIT-LIFT-PASS positive_additions={positive} "
        f"negative_additions={negative} final_empty=1"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

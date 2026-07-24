#!/usr/bin/env python3
"""Backward-slice and deterministically renumber a RUP-only LRAT proof.

The output CNF contains exactly the original clauses reachable from the final
empty-clause derivation.  The output LRAT contains exactly the reachable
additions, in their original order, with all identifiers and hints remapped.
Deterministic deletion records are inserted immediately after each retained
clause's last hint use so downstream kernel importers can bound live state.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import lzma
import tempfile
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import BinaryIO, Iterator


class MinimizeError(ValueError):
    """Raised when an input is not a well-formed proof in the supported class."""


@dataclass(frozen=True)
class CnfInfo:
    variables: int
    clauses: int
    raw_bytes: int
    raw_sha256: str
    container_bytes: int
    container_sha256: str


@dataclass(frozen=True)
class AdditionIndex:
    identifier: int
    offset: int
    line_number: int
    empty: bool


@dataclass(frozen=True)
class ProofInfo:
    additions: tuple[AdditionIndex, ...]
    final_identifier: int
    raw_bytes: int
    raw_sha256: str
    container_bytes: int
    container_sha256: str


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


@contextmanager
def open_input(path: Path) -> Iterator[BinaryIO]:
    if path.suffix == ".xz":
        with lzma.open(path, "rb") as stream:
            yield stream
    else:
        with path.open("rb") as stream:
            yield stream


def ascii_fields(raw_line: bytes, *, kind: str, line_number: int) -> list[str]:
    try:
        return raw_line.decode("ascii").split()
    except UnicodeDecodeError as error:
        raise MinimizeError(f"non-ASCII {kind} line {line_number}") from error


def parse_int(token: str, *, context: str) -> int:
    try:
        return int(token)
    except ValueError as error:
        raise MinimizeError(f"bad integer {token!r} in {context}") from error


def parse_clause_fields(
    fields: list[str], *, variables: int, context: str
) -> tuple[int, ...]:
    if not fields or fields[-1] != "0" or "0" in fields[:-1]:
        raise MinimizeError(f"missing or misplaced clause terminator in {context}")
    literals = tuple(parse_int(token, context=context) for token in fields[:-1])
    if any(literal == 0 or abs(literal) > variables for literal in literals):
        raise MinimizeError(f"literal outside declared range in {context}")
    if len(set(literals)) != len(literals) or any(-literal in literals for literal in literals):
        raise MinimizeError(f"duplicate or tautological clause in {context}")
    return literals


def scan_cnf(path: Path) -> CnfInfo:
    variables: int | None = None
    declared_clauses: int | None = None
    clause_count = 0
    raw_bytes = 0
    raw_digest = hashlib.sha256()
    with open_input(path) as stream:
        for line_number, raw_line in enumerate(stream, start=1):
            raw_bytes += len(raw_line)
            raw_digest.update(raw_line)
            fields = ascii_fields(raw_line, kind="DIMACS", line_number=line_number)
            if not fields or fields[0] == "c":
                continue
            if fields[0] == "p":
                if variables is not None or len(fields) != 4 or fields[1] != "cnf":
                    raise MinimizeError(f"bad DIMACS header on line {line_number}")
                variables = parse_int(fields[2], context=f"DIMACS line {line_number}")
                declared_clauses = parse_int(
                    fields[3], context=f"DIMACS line {line_number}"
                )
                if variables < 0 or declared_clauses < 1:
                    raise MinimizeError("invalid DIMACS dimensions")
                continue
            if variables is None:
                raise MinimizeError(f"clause before DIMACS header on line {line_number}")
            parse_clause_fields(
                fields, variables=variables, context=f"DIMACS line {line_number}"
            )
            clause_count += 1
    if variables is None or declared_clauses != clause_count:
        raise MinimizeError(
            f"DIMACS clause count mismatch: declared {declared_clauses}, found {clause_count}"
        )
    return CnfInfo(
        variables=variables,
        clauses=clause_count,
        raw_bytes=raw_bytes,
        raw_sha256=raw_digest.hexdigest(),
        container_bytes=path.stat().st_size,
        container_sha256=sha256_path(path),
    )


def parse_addition_fields(
    fields: list[str], *, variables: int, line_number: int
) -> tuple[int, tuple[int, ...], tuple[int, ...]]:
    context = f"LRAT line {line_number}"
    if len(fields) < 4:
        raise MinimizeError(f"malformed addition on {context}")
    identifier = parse_int(fields[0], context=context)
    try:
        first_zero = fields.index("0", 1)
        second_zero = fields.index("0", first_zero + 1)
    except ValueError as error:
        raise MinimizeError(f"malformed addition on {context}") from error
    if second_zero != len(fields) - 1:
        raise MinimizeError(f"trailing LRAT tokens on {context}")
    literals = parse_clause_fields(
        fields[1 : first_zero + 1], variables=variables, context=context
    )
    hints = tuple(
        parse_int(token, context=context) for token in fields[first_zero + 1 : second_zero]
    )
    if not hints:
        raise MinimizeError(f"addition has no RUP hints on {context}")
    if any(hint <= 0 for hint in hints):
        raise MinimizeError(f"RAT or nonpositive hint on {context}")
    return identifier, literals, hints


def index_proof(path: Path, cnf: CnfInfo, scratch: BinaryIO) -> ProofInfo:
    additions: list[AdditionIndex] = []
    known_derived: set[int] = set()
    last_addition = cnf.clauses
    final_identifier: int | None = None
    raw_bytes = 0
    raw_digest = hashlib.sha256()

    with open_input(path) as stream:
        for line_number, raw_line in enumerate(stream, start=1):
            raw_bytes += len(raw_line)
            raw_digest.update(raw_line)
            offset = scratch.tell()
            scratch.write(raw_line)
            fields = ascii_fields(raw_line, kind="LRAT", line_number=line_number)
            if not fields or fields[0] == "c":
                continue
            context = f"LRAT line {line_number}"
            identifier = parse_int(fields[0], context=context)
            if len(fields) >= 2 and fields[1] == "d":
                if identifier != last_addition:
                    raise MinimizeError(f"mislabelled deletion on {context}")
                if len(fields) < 3 or fields[-1] != "0" or "0" in fields[2:-1]:
                    raise MinimizeError(f"unterminated deletion on {context}")
                deleted = [parse_int(token, context=context) for token in fields[2:-1]]
                if any(clause_id <= 0 for clause_id in deleted):
                    raise MinimizeError(f"nonpositive deletion identifier on {context}")
                continue

            if final_identifier is not None:
                raise MinimizeError("addition occurs after the first empty-clause derivation")
            identifier, literals, hints = parse_addition_fields(
                fields, variables=cnf.variables, line_number=line_number
            )
            if identifier <= last_addition:
                raise MinimizeError(f"nonincreasing addition identifier on {context}")
            for hint in hints:
                if hint > cnf.clauses and hint not in known_derived:
                    raise MinimizeError(f"hint references missing or future clause {hint} on {context}")
            additions.append(
                AdditionIndex(
                    identifier=identifier,
                    offset=offset,
                    line_number=line_number,
                    empty=not literals,
                )
            )
            known_derived.add(identifier)
            last_addition = identifier
            if not literals:
                final_identifier = identifier

    scratch.flush()
    if final_identifier is None:
        raise MinimizeError("LRAT proof did not derive the empty clause")
    return ProofInfo(
        additions=tuple(additions),
        final_identifier=final_identifier,
        raw_bytes=raw_bytes,
        raw_sha256=raw_digest.hexdigest(),
        container_bytes=path.stat().st_size,
        container_sha256=sha256_path(path),
    )


def read_indexed_addition(
    scratch: BinaryIO, index: AdditionIndex, variables: int
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    scratch.seek(index.offset)
    raw_line = scratch.readline()
    fields = ascii_fields(raw_line, kind="LRAT", line_number=index.line_number)
    identifier, literals, hints = parse_addition_fields(
        fields, variables=variables, line_number=index.line_number
    )
    if identifier != index.identifier:
        raise MinimizeError("internal proof-index mismatch")
    return literals, hints


def backward_slice(
    proof: ProofInfo, cnf: CnfInfo, scratch: BinaryIO
) -> tuple[list[int], list[AdditionIndex]]:
    needed: set[int] = {proof.final_identifier}
    retained_reversed: list[AdditionIndex] = []
    for index in reversed(proof.additions):
        if index.identifier not in needed:
            continue
        _, hints = read_indexed_addition(scratch, index, cnf.variables)
        retained_reversed.append(index)
        needed.update(hints)

    retained = list(reversed(retained_reversed))
    retained_ids = {index.identifier for index in retained}
    missing = sorted(
        clause_id
        for clause_id in needed
        if clause_id > cnf.clauses and clause_id not in retained_ids
    )
    if missing:
        raise MinimizeError(f"backward slice has missing derived antecedents: {missing[:8]}")
    originals = sorted(clause_id for clause_id in needed if clause_id <= cnf.clauses)
    if not originals:
        raise MinimizeError("backward slice contains no original clauses")
    if not retained or retained[-1].identifier != proof.final_identifier:
        raise MinimizeError("backward slice lost the final empty clause")
    return originals, retained


def selected_original_clauses(
    path: Path, cnf: CnfInfo, selected: set[int]
) -> Iterator[tuple[int, tuple[int, ...]]]:
    variables: int | None = None
    clause_id = 0
    with open_input(path) as stream:
        for line_number, raw_line in enumerate(stream, start=1):
            fields = ascii_fields(raw_line, kind="DIMACS", line_number=line_number)
            if not fields or fields[0] == "c":
                continue
            if fields[0] == "p":
                variables = cnf.variables
                continue
            if variables is None:
                raise MinimizeError("clause before header during output pass")
            clause_id += 1
            if clause_id in selected:
                yield clause_id, parse_clause_fields(
                    fields, variables=variables, context=f"DIMACS line {line_number}"
                )


def format_clause(literals: tuple[int, ...]) -> str:
    if literals:
        return " ".join(map(str, literals)) + " 0\n"
    return "0\n"


def write_outputs(
    *,
    source_cnf: Path,
    cnf: CnfInfo,
    proof: ProofInfo,
    scratch: BinaryIO,
    originals: list[int],
    retained: list[AdditionIndex],
    output_cnf: Path,
    output_proof: Path,
) -> tuple[dict[int, int], int]:
    mapping: dict[int, int] = {
        old_identifier: new_identifier
        for new_identifier, old_identifier in enumerate(originals, start=1)
    }
    next_identifier = len(originals) + 1
    for index in retained:
        mapping[index.identifier] = next_identifier
        next_identifier += 1

    last_use: dict[int, int] = {}
    for index in retained:
        _, hints = read_indexed_addition(scratch, index, cnf.variables)
        new_identifier = mapping[index.identifier]
        for hint in hints:
            last_use[mapping[hint]] = new_identifier
    deletions_at: dict[int, set[int]] = {}
    for clause_identifier, step_identifier in last_use.items():
        deletions_at.setdefault(step_identifier, set()).add(clause_identifier)

    output_cnf.parent.mkdir(parents=True, exist_ok=True)
    output_proof.parent.mkdir(parents=True, exist_ok=True)
    with output_cnf.open("w", encoding="ascii", newline="\n") as stream:
        stream.write(f"p cnf {cnf.variables} {len(originals)}\n")
        emitted = 0
        for old_identifier, literals in selected_original_clauses(
            source_cnf, cnf, set(originals)
        ):
            if old_identifier not in mapping:
                raise MinimizeError("internal original-clause map mismatch")
            stream.write(format_clause(literals))
            emitted += 1
        if emitted != len(originals):
            raise MinimizeError("failed to emit every selected original clause")

    emitted_deletions = 0
    with output_proof.open("w", encoding="ascii", newline="\n") as stream:
        for index in retained:
            literals, hints = read_indexed_addition(scratch, index, cnf.variables)
            try:
                remapped_hints = tuple(mapping[hint] for hint in hints)
            except KeyError as error:
                raise MinimizeError(f"unmapped reachable hint {error.args[0]}") from error
            literal_text = " ".join(map(str, literals))
            hint_text = " ".join(map(str, remapped_hints))
            prefix = f"{mapping[index.identifier]}"
            if literal_text:
                stream.write(f"{prefix} {literal_text} 0 {hint_text} 0\n")
            else:
                stream.write(f"{prefix} 0 {hint_text} 0\n")
            if literals:
                deletions = sorted(deletions_at.get(mapping[index.identifier], set()))
                if deletions:
                    stream.write(
                        f"{prefix} d {' '.join(map(str, deletions))} 0\n"
                    )
                    emitted_deletions += len(deletions)
    return mapping, emitted_deletions


def minimize(
    *,
    source_cnf: Path,
    source_proof: Path,
    output_cnf: Path,
    output_proof: Path,
    map_path: Path,
    receipt_path: Path,
) -> dict[str, object]:
    cnf = scan_cnf(source_cnf)
    with tempfile.TemporaryFile(mode="w+b") as scratch:
        proof = index_proof(source_proof, cnf, scratch)
        originals, retained = backward_slice(proof, cnf, scratch)
        mapping, emitted_deletions = write_outputs(
            source_cnf=source_cnf,
            cnf=cnf,
            proof=proof,
            scratch=scratch,
            originals=originals,
            retained=retained,
            output_cnf=output_cnf,
            output_proof=output_proof,
        )

    map_document = {
        "schema_version": 1,
        "original_clause_ids": originals,
        "derived_clause_ids": [index.identifier for index in retained],
        "old_to_new": {str(old): mapping[old] for old in sorted(mapping)},
    }
    map_path.parent.mkdir(parents=True, exist_ok=True)
    map_path.write_text(
        json.dumps(map_document, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    receipt: dict[str, object] = {
        "schema_version": 1,
        "mode": "backward-rup-core",
        "source": {
            "cnf_path": str(source_cnf),
            "cnf_container_bytes": cnf.container_bytes,
            "cnf_container_sha256": cnf.container_sha256,
            "cnf_raw_bytes": cnf.raw_bytes,
            "cnf_raw_sha256": cnf.raw_sha256,
            "proof_path": str(source_proof),
            "proof_container_bytes": proof.container_bytes,
            "proof_container_sha256": proof.container_sha256,
            "proof_raw_bytes": proof.raw_bytes,
            "proof_raw_sha256": proof.raw_sha256,
            "variables": cnf.variables,
            "original_clauses": cnf.clauses,
            "additions": len(proof.additions),
        },
        "core": {
            "cnf_path": str(output_cnf),
            "cnf_bytes": output_cnf.stat().st_size,
            "cnf_sha256": sha256_path(output_cnf),
            "proof_path": str(output_proof),
            "proof_bytes": output_proof.stat().st_size,
            "proof_sha256": sha256_path(output_proof),
            "map_path": str(map_path),
            "map_bytes": map_path.stat().st_size,
            "map_sha256": sha256_path(map_path),
            "original_clauses": len(originals),
            "additions": len(retained),
            "deleted_clauses": emitted_deletions,
            "final_clause_id": mapping[proof.final_identifier],
            "rat_additions": 0,
        },
    }
    receipt_path.parent.mkdir(parents=True, exist_ok=True)
    receipt_path.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    return receipt


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--output-cnf", type=Path, required=True)
    parser.add_argument("--output-proof", type=Path, required=True)
    parser.add_argument("--map", dest="map_path", type=Path, required=True)
    parser.add_argument("--receipt", dest="receipt_path", type=Path, required=True)
    args = parser.parse_args()
    try:
        receipt = minimize(
            source_cnf=args.cnf,
            source_proof=args.proof,
            output_cnf=args.output_cnf,
            output_proof=args.output_proof,
            map_path=args.map_path,
            receipt_path=args.receipt_path,
        )
    except (OSError, EOFError, lzma.LZMAError, MinimizeError) as error:
        raise SystemExit(f"RUP-CORE-FAILED: {error}") from error
    core = receipt["core"]
    source = receipt["source"]
    assert isinstance(core, dict) and isinstance(source, dict)
    print(
        "RUP-CORE-PASS "
        f"original_clauses={source['original_clauses']} "
        f"core_clauses={core['original_clauses']} "
        f"original_additions={source['additions']} "
        f"core_additions={core['additions']} rat_additions=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

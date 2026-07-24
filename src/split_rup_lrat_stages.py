#!/usr/bin/env python3
"""Split a RUP-only LRAT proof into deterministic live-frontier stages."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.minimize_rup_lrat import (
    MinimizeError,
    ascii_fields,
    open_input,
    parse_addition_fields,
    parse_clause_fields,
    parse_int,
    scan_cnf,
    sha256_path,
)


class SplitError(ValueError):
    """Raised when a proof cannot be partitioned without changing its semantics."""


def normalized_addition(
    identifier: int, literals: tuple[int, ...], hints: tuple[int, ...]
) -> str:
    literal_text = " ".join(map(str, literals))
    hint_text = " ".join(map(str, hints))
    prefix = f"{identifier} {literal_text} 0" if literals else f"{identifier} 0"
    return f"{prefix} {hint_text} 0\n"


def normalized_deletion(label: int, identifiers: list[int]) -> str:
    return f"{label} d {' '.join(map(str, identifiers))} 0\n"


def frontier_text(live: dict[int, tuple[int, ...]]) -> str:
    records: list[str] = []
    for identifier in sorted(live):
        literals = live[identifier]
        literal_text = " ".join(map(str, literals))
        records.append(
            f"{identifier} {literal_text} 0\n" if literals else f"{identifier} 0\n"
        )
    return "".join(records)


def digest(path: Path) -> dict[str, object]:
    return {"bytes": path.stat().st_size, "sha256": sha256_path(path)}


def read_cnf(path: Path) -> tuple[int, dict[int, tuple[int, ...]]]:
    info = scan_cnf(path)
    live: dict[int, tuple[int, ...]] = {}
    clause_identifier = 0
    with open_input(path) as stream:
        for line_number, raw_line in enumerate(stream, start=1):
            fields = ascii_fields(raw_line, kind="DIMACS", line_number=line_number)
            if not fields or fields[0] == "c" or fields[0] == "p":
                continue
            clause_identifier += 1
            live[clause_identifier] = parse_clause_fields(
                fields,
                variables=info.variables,
                context=f"DIMACS line {line_number}",
            )
    if clause_identifier != info.clauses:
        raise SplitError("internal CNF clause-count mismatch")
    return info.variables, live


def split_proof(
    *, cnf_path: Path, proof_path: Path, output_directory: Path, stage_size: int
) -> dict[str, object]:
    if stage_size < 1:
        raise SplitError("stage size must be positive")
    output_directory.mkdir(parents=True, exist_ok=True)
    if any(output_directory.iterdir()):
        raise SplitError(f"output directory is not empty: {output_directory}")

    variables, live = read_cnf(cnf_path)
    original_clauses = len(live)
    last_addition = original_clauses
    stage = 0
    stage_additions = 0
    total_additions = 0
    saw_empty = False
    chunk: list[str] = []
    records: list[dict[str, object]] = []

    def finish_stage(*, final: bool) -> None:
        nonlocal stage, stage_additions, chunk
        if stage_additions == 0:
            raise SplitError("cannot emit a stage with no additions")
        chunk_path = output_directory / f"stage_{stage:03d}.lrat"
        frontier_path = output_directory / f"stage_{stage:03d}.frontier"
        chunk_path.write_text("".join(chunk), encoding="ascii", newline="\n")
        frontier_path.write_text(frontier_text(live), encoding="ascii", newline="\n")
        records.append(
            {
                "stage": stage,
                "additions": stage_additions,
                "cumulative_additions": total_additions,
                "frontier_clauses": len(live),
                "final": final,
                "chunk": {"path": chunk_path.name, **digest(chunk_path)},
                "frontier": {"path": frontier_path.name, **digest(frontier_path)},
            }
        )
        stage += 1
        stage_additions = 0
        chunk = []

    with open_input(proof_path) as stream:
        for line_number, raw_line in enumerate(stream, start=1):
            fields = ascii_fields(raw_line, kind="LRAT", line_number=line_number)
            if not fields or fields[0] == "c":
                continue
            context = f"LRAT line {line_number}"
            identifier = parse_int(fields[0], context=context)
            is_deletion = len(fields) >= 2 and fields[1] == "d"
            if is_deletion:
                if identifier != last_addition:
                    raise SplitError(f"mislabelled deletion on {context}")
                if len(fields) < 4 or fields[-1] != "0" or "0" in fields[2:-1]:
                    raise SplitError(f"malformed deletion on {context}")
                deleted = [parse_int(token, context=context) for token in fields[2:-1]]
                if len(set(deleted)) != len(deleted) or any(item <= 0 for item in deleted):
                    raise SplitError(f"invalid deletion identifiers on {context}")
                for item in deleted:
                    if item not in live:
                        raise SplitError(f"deletion of non-live clause {item} on {context}")
                    del live[item]
                chunk.append(normalized_deletion(identifier, deleted))
                continue

            if saw_empty:
                raise SplitError("addition occurs after the empty clause")
            if stage_additions == stage_size:
                finish_stage(final=False)
            try:
                identifier, literals, hints = parse_addition_fields(
                    fields, variables=variables, line_number=line_number
                )
            except MinimizeError as error:
                raise SplitError(str(error)) from error
            if identifier <= last_addition:
                raise SplitError(f"nonincreasing addition identifier on {context}")
            missing = [hint for hint in hints if hint not in live]
            if missing:
                raise SplitError(f"non-live hints {missing[:8]} on {context}")
            if identifier in live:
                raise SplitError(f"reused live identifier {identifier} on {context}")
            live[identifier] = literals
            last_addition = identifier
            stage_additions += 1
            total_additions += 1
            chunk.append(normalized_addition(identifier, literals, hints))
            saw_empty = not literals

    if not saw_empty:
        raise SplitError("proof did not derive the empty clause")
    finish_stage(final=True)
    if sum(int(record["additions"]) for record in records) != total_additions:
        raise SplitError("stage addition accounting mismatch")
    if [record["stage"] for record in records] != list(range(len(records))):
        raise SplitError("nonconsecutive stage numbering")

    receipt: dict[str, object] = {
        "schema_version": 1,
        "stage_size": stage_size,
        "original_clauses": original_clauses,
        "total_additions": total_additions,
        "stages": records,
        "source": {
            "cnf": {"path": str(cnf_path), **digest(cnf_path)},
            "proof": {"path": str(proof_path), **digest(proof_path)},
        },
    }
    receipt_path = output_directory / "receipt.json"
    receipt_path.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="ascii"
    )
    return receipt


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--proof", type=Path, required=True)
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--stage-size", type=int, default=10_000)
    args = parser.parse_args()
    try:
        receipt = split_proof(
            cnf_path=args.cnf.resolve(),
            proof_path=args.proof.resolve(),
            output_directory=args.output_directory.resolve(),
            stage_size=args.stage_size,
        )
    except (OSError, MinimizeError, SplitError) as error:
        raise SystemExit(f"RUP-STAGE-SPLIT-FAILED: {error}") from error
    print(
        "RUP-STAGE-SPLIT-PASS "
        f"stages={len(receipt['stages'])} additions={receipt['total_additions']} "
        f"stage_size={receipt['stage_size']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

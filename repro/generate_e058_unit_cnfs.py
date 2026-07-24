#!/usr/bin/env python3
"""Extract exact primary unit assignments for the E058 Lean bridge.

The reduced LRAT cores need the branch assumptions from their full source
formulas, including units that backward core minimization legitimately
deleted.  This script streams each pinned XZ source formula, verifies its raw
SHA-256 and dimensions against the independently reproduced core receipt, and
writes a tiny comment-free DIMACS file containing only primary edge units.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import lzma
from pathlib import Path

PRIMARY_VARIABLES = 26 * 25 // 2


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def extract_units(
    source_path: Path,
    expected_sha256: str,
    expected_variables: int,
    expected_clauses: int,
) -> list[int]:
    digest = hashlib.sha256()
    header: tuple[int, int] | None = None
    clause_count = 0
    units: list[int] = []
    seen: set[int] = set()
    with lzma.open(source_path, "rb") as stream:
        for raw_line in stream:
            digest.update(raw_line)
            line = raw_line.decode("ascii").strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p "):
                fields = line.split()
                if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                    raise ValueError(f"{source_path}: malformed DIMACS header")
                header = (int(fields[2]), int(fields[3]))
                continue
            if header is None:
                raise ValueError(f"{source_path}: clause before header")
            fields = [int(field) for field in line.split()]
            if not fields or fields[-1] != 0 or 0 in fields[:-1]:
                raise ValueError(f"{source_path}: malformed clause")
            clause_count += 1
            literals = fields[:-1]
            if len(literals) == 1 and 1 <= abs(literals[0]) <= PRIMARY_VARIABLES:
                literal = literals[0]
                if -literal in seen:
                    raise ValueError(
                        f"{source_path}: contradictory primary units for {abs(literal)}"
                    )
                if literal not in seen:
                    seen.add(literal)
                    units.append(literal)
    actual_sha256 = digest.hexdigest()
    if actual_sha256 != expected_sha256:
        raise ValueError(
            f"{source_path}: raw SHA-256 {actual_sha256}, expected {expected_sha256}"
        )
    if header != (expected_variables, expected_clauses):
        raise ValueError(
            f"{source_path}: header {header}, expected "
            f"{(expected_variables, expected_clauses)}"
        )
    if clause_count != expected_clauses:
        raise ValueError(
            f"{source_path}: parsed {clause_count} clauses, expected {expected_clauses}"
        )
    return units


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--receipt-directory", type=Path, required=True)
    parser.add_argument("--repository", type=Path, default=Path.cwd())
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()

    repository = args.repository.resolve()
    args.output_directory.mkdir(parents=True, exist_ok=True)
    records: list[dict[str, object]] = []
    receipt_paths = sorted(args.receipt_directory.glob("*.receipt.json"))
    if not receipt_paths:
        raise ValueError("no E058 core receipts found")

    for receipt_path in receipt_paths:
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        label = receipt["label"]
        source = receipt["source"]
        source_path = repository / source["cnf_path"]
        units = extract_units(
            source_path,
            source["cnf_raw_sha256"],
            source["variables"],
            source["original_clauses"],
        )
        output_path = args.output_directory / f"{label}.cnf"
        body = [f"p cnf {source['variables']} {len(units)}"]
        body.extend(f"{literal} 0" for literal in units)
        output_path.write_text("\n".join(body) + "\n", encoding="ascii", newline="\n")
        records.append(
            {
                "label": label,
                "source_container": source["cnf_path"],
                "source_raw_sha256": source["cnf_raw_sha256"],
                "source_variables": source["variables"],
                "source_clauses": source["original_clauses"],
                "unit_count": len(units),
                "positive_units": sum(literal > 0 for literal in units),
                "negative_units": sum(literal < 0 for literal in units),
                "unit_cnf": str(output_path.relative_to(repository)),
                "unit_cnf_bytes": output_path.stat().st_size,
                "unit_cnf_sha256": sha256_file(output_path),
            }
        )
        print(
            "E058-UNIT-CNF-PASS "
            f"label={label} units={len(units)} "
            f"sha256={records[-1]['unit_cnf_sha256']}"
        )

    manifest = {
        "schema_version": 1,
        "scope": "E058 exact primary edge-unit assignments",
        "primary_variables": PRIMARY_VARIABLES,
        "records": records,
    }
    args.manifest.parent.mkdir(parents=True, exist_ok=True)
    args.manifest.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    print(
        "E058-UNIT-MANIFEST-PASS "
        f"records={len(records)} sha256={sha256_file(args.manifest)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

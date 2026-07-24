#!/usr/bin/env python3
"""Generate and adversarially dual-check all 89 E058 RUP proof cores."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.minimize_rup_lrat import minimize  # noqa: E402

E042_DIRECT = [0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18]


@dataclass(frozen=True)
class CoreJob:
    label: str
    cnf: Path
    proof: Path
    expected: dict[str, object]


def digest(path: Path) -> tuple[int, str]:
    hasher = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            size += len(block)
            hasher.update(block)
    return size, hasher.hexdigest()


def read_receipt(relative: str) -> dict[str, object]:
    return json.loads((REPOSITORY / relative).read_text(encoding="ascii"))


def inventory() -> list[CoreJob]:
    jobs: list[CoreJob] = []
    e038 = read_receipt("artifacts/e038_brooks_branches/receipt.json")
    if e038["certified_branches"] != list(range(19)):
        raise AssertionError("E038 certified inventory differs")
    for record in e038["records"]:
        branch = int(record["branch"])
        stem = f"branch_{branch:02d}"
        jobs.append(
            CoreJob(
                label=f"e038_{stem}",
                cnf=Path(f"artifacts/e038_brooks_branches/{stem}.cnf.xz"),
                proof=Path(f"certificates/e038_brooks_branches/{stem}.lrat.xz"),
                expected=record,
            )
        )

    e042 = read_receipt("artifacts/e042_branch19_cross_patterns/receipt.json")
    if e042["certified_children"] != E042_DIRECT:
        raise AssertionError("E042 direct inventory differs")
    for record in e042["records"]:
        if record["status"] != "CERTIFIED":
            continue
        child = int(record["child"])
        stem = f"child_{child:02d}"
        jobs.append(
            CoreJob(
                label=f"e042_{stem}",
                cnf=Path(f"artifacts/e042_branch19_cross_patterns/{stem}.cnf.xz"),
                proof=Path(f"certificates/e042_branch19_cross_patterns/{stem}.lrat.xz"),
                expected=record,
            )
        )

    e043 = read_receipt("artifacts/e043_branch19_zero_neighborhoods/receipt.json")
    certified_e043 = {tuple(pair) for pair in e043["certified_children"]}
    observed_e043: set[tuple[int, int]] = set()
    for record in e043["records"]:
        parent = int(record["parent"])
        child = int(record["child"])
        observed_e043.add((parent, child))
        stem = f"parent_{parent:02d}_child_{child:02d}"
        jobs.append(
            CoreJob(
                label=f"e043_{stem}",
                cnf=Path(f"artifacts/e043_branch19_zero_neighborhoods/{stem}.cnf.xz"),
                proof=Path(f"certificates/e043_branch19_zero_neighborhoods/{stem}.lrat.xz"),
                expected=record,
            )
        )
    if observed_e043 != certified_e043 or len(observed_e043) != 47:
        raise AssertionError("E043 certified inventory differs")

    e045 = read_receipt("artifacts/e045_zero_anchor_quotients/receipt.json")
    if e045["certified_branches"] != list(range(20, 26)):
        raise AssertionError("E045 certified inventory differs")
    for record in e045["records"]:
        branch = int(record["branch"])
        stem = f"branch_{branch:02d}"
        jobs.append(
            CoreJob(
                label=f"e045_{stem}",
                cnf=Path(f"artifacts/e045_zero_anchor_quotients/{stem}.cnf.xz"),
                proof=Path(f"certificates/e045_zero_anchor_quotients/{stem}.lrat.xz"),
                expected=record,
            )
        )

    labels = [job.label for job in jobs]
    if len(jobs) != 89 or len(set(labels)) != 89:
        raise AssertionError("combined E058 inventory is not exactly 89 distinct jobs")
    return jobs


def verify_source(job: CoreJob, item: dict[str, object]) -> None:
    source = item["source"]
    assert isinstance(source, dict)
    expected = job.expected
    comparisons = {
        "cnf_container_bytes": "cnf_xz_bytes",
        "cnf_container_sha256": "cnf_xz_sha256",
        "cnf_raw_bytes": "cnf_raw_bytes",
        "cnf_raw_sha256": "cnf_raw_sha256",
        "proof_container_bytes": "lrat_xz_bytes",
        "proof_container_sha256": "lrat_xz_sha256",
        "proof_raw_bytes": "lrat_raw_bytes",
        "proof_raw_sha256": "lrat_raw_sha256",
    }
    for actual_key, expected_key in comparisons.items():
        if source[actual_key] != expected[expected_key]:
            raise AssertionError(
                f"{job.label}: source receipt mismatch for {actual_key}: "
                f"{source[actual_key]} != {expected[expected_key]}"
            )
    if expected.get("converter_zero_rat", True) is not True:
        raise AssertionError(f"{job.label}: source receipt is not zero-RAT")


def require(command: list[str], accepted: bool, label: str) -> str:
    result = subprocess.run(command, capture_output=True, text=True)
    if (result.returncode == 0) != accepted:
        raise AssertionError(
            f"{label}: return={result.returncode}\n"
            f"stdout={result.stdout}\nstderr={result.stderr}"
        )
    return result.stdout.strip()


def corruptions(proof: Path, directory: Path) -> tuple[Path, Path]:
    lines = proof.read_bytes().splitlines(keepends=True)
    if not lines or not lines[-1].endswith(b"\n"):
        raise AssertionError("core LRAT lacks complete record boundaries")
    truncated = directory / "truncated.lrat"
    forged = directory / "forged.lrat"
    truncated.write_bytes(b"".join(lines[:-1]))
    final_fields = lines[-1].decode("ascii").split()
    final_identifier = int(final_fields[0])
    forged.write_bytes(b"".join(lines[:-1]))
    with forged.open("a", encoding="ascii", newline="\n") as stream:
        stream.write(f"{final_identifier} 0 1 0\n")
    return truncated, forged


def generate_all(
    *, output_directory: Path, c_checker: Path, python_checker: Path, only: set[str]
) -> dict[str, object]:
    jobs = inventory()
    if only:
        unknown = only - {job.label for job in jobs}
        if unknown:
            raise AssertionError(f"unknown --only labels: {sorted(unknown)}")
        jobs = [job for job in jobs if job.label in only]
    output_directory.mkdir(parents=True, exist_ok=True)
    if any(output_directory.iterdir()):
        raise AssertionError(f"output directory is not empty: {output_directory}")
    if not c_checker.is_file() or not python_checker.is_file():
        raise AssertionError("one or both LRAT checkers are missing")

    records: list[dict[str, object]] = []
    negative_checks = 0
    with tempfile.TemporaryDirectory(prefix="erdos617-e058-corrupt-") as temporary:
        corruption_directory = Path(temporary)
        for ordinal, job in enumerate(jobs, start=1):
            output_cnf = output_directory / f"{job.label}.cnf"
            output_proof = output_directory / f"{job.label}.lrat"
            map_path = output_directory / f"{job.label}.map.json"
            item_receipt_path = output_directory / f"{job.label}.receipt.json"
            item = minimize(
                source_cnf=REPOSITORY / job.cnf,
                source_proof=REPOSITORY / job.proof,
                output_cnf=output_cnf,
                output_proof=output_proof,
                map_path=map_path,
                receipt_path=item_receipt_path,
            )
            verify_source(job, item)
            c_output = require(
                [str(c_checker), str(output_cnf), str(output_proof)],
                True,
                f"{job.label}: C checker",
            )
            python_output = require(
                [sys.executable, str(python_checker), str(output_cnf), str(output_proof)],
                True,
                f"{job.label}: Python checker",
            )
            truncated, forged = corruptions(output_proof, corruption_directory)
            for corruption_name, corruption in (("truncated", truncated), ("forged", forged)):
                for checker_name, command in (
                    ("C", [str(c_checker), str(output_cnf), str(corruption)]),
                    (
                        "Python",
                        [sys.executable, str(python_checker), str(output_cnf), str(corruption)],
                    ),
                ):
                    require(
                        command,
                        False,
                        f"{job.label}: {checker_name} {corruption_name}",
                    )
                    negative_checks += 1
            truncated.unlink()
            forged.unlink()

            item["label"] = job.label
            item["source"]["cnf_path"] = str(job.cnf)
            item["source"]["proof_path"] = str(job.proof)
            item["core"]["cnf_path"] = output_cnf.name
            item["core"]["proof_path"] = output_proof.name
            item["core"]["map_path"] = map_path.name
            item["c_checker_output"] = c_output
            item["python_checker_output"] = python_output
            item_receipt_path.write_text(
                json.dumps(item, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
            records.append(item)
            print(
                f"E058-RUP-CORE-{ordinal:02d}-OF-{len(jobs)}-PASS "
                f"label={job.label} clauses={item['core']['original_clauses']} "
                f"additions={item['core']['additions']}",
                flush=True,
            )

    receipt: dict[str, object] = {
        "schema_version": 1,
        "experiment": "E058-R5-SPECIAL-BROOKS-KERNEL-BRIDGE",
        "inventory_count": len(records),
        "full_inventory": not only,
        "rup_only": True,
        "c_checks": len(records),
        "python_checks": len(records),
        "negative_checks": negative_checks,
        "tool_sha256": {
            "minimizer": digest(REPOSITORY / "src/minimize_rup_lrat.py")[1],
            "c_lrat_checker": digest(c_checker)[1],
            "python_lrat_checker": digest(python_checker)[1],
        },
        "python": platform.python_version(),
        "records": records,
    }
    receipt_path = output_directory / "receipt.json"
    receipt_path.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(
        "E058-RUP-CORES-PASS "
        f"cores={len(records)} c_checks={len(records)} python_checks={len(records)} "
        f"negative_checks={negative_checks} zero_rat={len(records)}"
    )
    return receipt


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument(
        "--c-checker", type=Path, default=REPOSITORY / "build/lrat-check-upstream"
    )
    parser.add_argument(
        "--python-checker", type=Path, default=REPOSITORY / "src/check_lrat.py"
    )
    parser.add_argument("--only", action="append", default=[])
    args = parser.parse_args()
    try:
        generate_all(
            output_directory=args.output_directory,
            c_checker=args.c_checker.resolve(),
            python_checker=args.python_checker.resolve(),
            only=set(args.only),
        )
    except (AssertionError, OSError, ValueError) as error:
        raise SystemExit(f"E058-RUP-CORES-FAILED: {error}") from error
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Validate the clean-start/resume provenance of a completed E058 audit."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

EXPECTED_LEGACY_RUNNER_SHA256 = (
    "c69d27f7ca1cc5c98c087c287f832ca9d1ed4925d21f4166f762af1c0b37fb72"
)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--transcript", type=Path, required=True)
    parser.add_argument("--final-receipt", type=Path, required=True)
    parser.add_argument("--executed-runner", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    transcript_path = args.transcript.resolve()
    final_receipt_path = args.final_receipt.resolve()
    runner_path = args.executed_runner.resolve()
    output_path = args.output.resolve()
    output_directory = output_path.parent
    input_paths = (transcript_path, final_receipt_path, runner_path)
    relative_inputs: dict[Path, str] = {}
    for input_path in input_paths:
        try:
            relative_inputs[input_path] = input_path.relative_to(
                output_directory
            ).as_posix()
        except ValueError as error:
            raise ValueError(
                "clean-start evidence inputs must be beside or below the "
                "sequence receipt"
            ) from error
    transcript = transcript_path.read_text(encoding="utf-8")
    receipt = json.loads(final_receipt_path.read_text(encoding="ascii"))

    clean_markers = (
        "E058-CERTIFICATE-REGENERATION-PASS certificates=3",
        "Build completed successfully (1315 jobs).",
        (
            "E058-RUP-CORES-PASS cores=89 c_checks=89 "
            "python_checks=89 negative_checks=356 zero_rat=89"
        ),
    )
    positions = [transcript.find(marker) for marker in clean_markers]
    first_resume = transcript.find("E058-FRESH-AUDIT-RESUME ")
    if (
        any(position < 0 for position in positions)
        or positions != sorted(positions)
        or first_resume < 0
        or positions[-1] > first_resume
    ):
        raise ValueError("clean-start markers are missing or out of order")
    if "warning:" in transcript.lower():
        raise ValueError("successful clean-start transcript contains a warning")

    terminal = re.findall(
        r"^E058-FRESH-LEAN-AUDIT-PASS .*receipt_sha256=([0-9a-f]{64})$",
        transcript,
        flags=re.MULTILINE,
    )
    receipt_sha256 = sha256_path(final_receipt_path)
    source_inventory = receipt.get("source_inventory", {})
    if terminal != [receipt_sha256]:
        raise ValueError("terminal pass marker does not bind the final receipt")
    if (
        receipt.get("verification") != "LEAN-KERNEL-FIXED-R5"
        or receipt.get("fresh_local_build") is not True
        or receipt.get("resumed_after_core_replay") is not True
        or receipt.get("cores", {}).get("count") != 89
        or receipt.get("kernel_imports", {}).get("count") != 89
        or receipt.get("semantic_closures", {}).get("count") != 89
        or receipt.get("axiom_queries", {}).get("count") != 192
        or receipt.get("axiom_queries", {}).get("final_theorem")
        != "Erdos617.e058Problem617AtFive"
        or set(receipt.get("axiom_queries", {}).get("final_axioms", []))
        != ALLOWED_AXIOMS
        or receipt.get("warnings") != 0
        or receipt.get("forbidden_source_hits") != 0
        or not isinstance(source_inventory.get("count"), int)
        or source_inventory.get("count", 0) <= 0
        or re.fullmatch(
            r"[0-9a-f]{64}",
            str(source_inventory.get("combined_sha256", "")),
        )
        is None
    ):
        raise ValueError("completed E058 receipt has the wrong scope")
    runner_sha256 = sha256_path(runner_path)
    embedded_runner_sha256 = receipt.get("audit_runner", {}).get(
        "sha256_at_start"
    )
    if embedded_runner_sha256 is None:
        if runner_sha256 != EXPECTED_LEGACY_RUNNER_SHA256:
            raise ValueError("legacy executed runner differs from its pinned hash")
        runner_binding = "PINNED-LEGACY-RUNNER-SHA256"
    elif embedded_runner_sha256 == runner_sha256:
        runner_binding = "SELF-HASHED-RUNNER-RECEIPT"
    else:
        raise ValueError("executed runner hash differs from the final receipt")

    output = {
        "schema_version": 1,
        "experiment": "E058-R5-SPECIAL-BROOKS-KERNEL-BRIDGE",
        "verification": "CLEAN-START-SEQUENCE-PROVENANCE",
        "complete": True,
        "scope": (
            "The successful sequence began after the runner's no-local-build "
            "gate, regenerated certificates and all cores, and later resumed "
            "only after the completed core replay."
        ),
        "fresh_local_build": True,
        "resumed_after_core_replay": True,
        "clean_start_markers": list(clean_markers),
        "resume_segments": transcript.count("E058-FRESH-AUDIT-RESUME "),
        "proof_counts": {
            "cores": 89,
            "kernel_imports": 89,
            "semantic_closures": 89,
            "axiom_queries": 192,
        },
        "axiom_queries": {
            "final_theorem": "Erdos617.e058Problem617AtFive",
            "final_axioms": sorted(ALLOWED_AXIOMS),
        },
        "source_inventory": source_inventory,
        "transcript": {
            "path": relative_inputs[transcript_path],
            "bytes": transcript_path.stat().st_size,
            "sha256": sha256_path(transcript_path),
        },
        "raw_audit_receipt": {
            "path": relative_inputs[final_receipt_path],
            "bytes": final_receipt_path.stat().st_size,
            "sha256": receipt_sha256,
        },
        "audit_runner": {
            "path": relative_inputs[runner_path],
            "bytes": runner_path.stat().st_size,
            "sha256_at_start": runner_sha256,
            "binding": runner_binding,
        },
        "warnings": 0,
        "forbidden_source_hits": 0,
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n",
        encoding="ascii",
        newline="\n",
    )
    print(
        "E058-CLEAN-START-SEQUENCE-PASS "
        f"resume_segments={output['resume_segments']} "
        f"receipt_sha256={sha256_path(output_path)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

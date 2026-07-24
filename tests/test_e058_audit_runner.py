from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from repro.run_e058_branch02_benchmark import (
    BenchmarkError,
    elapsed_seconds,
    lean_source,
    parse_resource_log,
    strip_dimacs_comments,
)
from repro.run_e058_special_brooks_kernel_audit import (
    AuditError,
    render_axiom_audit,
    validate_clean_start_receipt,
    validate_unit_manifest,
)


class E058AuditRunnerTests(unittest.TestCase):
    def test_branch02_benchmark_resource_parser_is_strict(self) -> None:
        report = """\
        User time (seconds): 201.09
        System time (seconds): 3.61
        Elapsed (wall clock) time (h:mm:ss or m:ss): 3:21.17
        Maximum resident set size (kbytes): 6172408
        Exit status: 0
"""
        observed = parse_resource_log(report)
        self.assertAlmostEqual(observed["elapsed_seconds"], 201.17)
        self.assertEqual(observed["max_rss_kb"], 6172408)
        self.assertEqual(elapsed_seconds("1:02:03.5"), 3723.5)
        with self.assertRaises(BenchmarkError):
            parse_resource_log("Exit status: 0\n")

    def test_branch02_benchmark_strips_only_pinned_comments(self) -> None:
        body = (
            b"c first\n"
            b"c second\n"
            b"p cnf 3930 474332\n"
            b"1 0\n"
        )
        observed, count = strip_dimacs_comments(body)
        self.assertEqual(count, 2)
        self.assertEqual(observed, b"p cnf 3930 474332\n1 0\n")
        with self.assertRaises(BenchmarkError):
            strip_dimacs_comments(body.replace(b"c second\n", b""))

    def test_branch02_benchmark_source_is_proof_only(self) -> None:
        source = lean_source(
            "E058Branch02RawProofOnly",
            Path(".e058-branch02-benchmark-work/raw.cnf"),
            Path(".e058-branch02-benchmark-work/raw.lrat"),
        )
        self.assertIn("Mathlib.Tactic.Sat.fromLRATAux", source)
        self.assertIn("#print axioms E058Branch02RawProofOnly", source)
        self.assertNotIn("Mathlib.Tactic.Sat.fromLRAT cnf", source)
        self.assertNotIn("/home/", source)

    def test_axiom_inventory_has_exact_designated_scope(self) -> None:
        labels = [f"label_{index:02d}" for index in range(89)]
        source, names = render_axiom_audit(labels)
        self.assertEqual(len(names), 192)
        self.assertEqual(len(set(names)), 192)
        self.assertIn("Erdos617.e058NoR5Counterexample", names)
        self.assertIn("Erdos617.e058Problem617AtFive", names)
        self.assertIn(
            "#print axioms Erdos617.e058NoR5Counterexample",
            source,
        )

    def test_clean_start_receipt_requires_complete_scope(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "receipt.json"
            receipt = {
                "verification": "LEAN-KERNEL-FIXED-R5",
                "fresh_local_build": True,
                "resumed_after_core_replay": False,
                "cores": {"count": 89},
                "kernel_imports": {"count": 89},
                "semantic_closures": {"count": 89},
                "axiom_queries": {
                    "count": 192,
                    "final_theorem": "Erdos617.e058Problem617AtFive",
                    "final_axioms": [
                        "propext",
                        "Classical.choice",
                        "Quot.sound",
                    ],
                },
                "warnings": 0,
                "forbidden_source_hits": 0,
                "source_inventory": {
                    "count": 1,
                    "combined_sha256": "0" * 64,
                },
                "audit_runner": {
                    "path": "repro/runner.py",
                    "sha256_at_start": "1" * 64,
                },
            }
            path.write_text(json.dumps(receipt), encoding="ascii")
            with self.assertRaisesRegex(
                AuditError,
                "CLEAN-START-SEQUENCE-PROVENANCE",
            ):
                validate_clean_start_receipt(path)
            runner_path = Path(temporary) / "runner.py"
            runner_path.write_text("# test runner\n", encoding="ascii")
            runner_sha256 = hashlib.sha256(runner_path.read_bytes()).hexdigest()
            receipt["audit_runner"]["sha256_at_start"] = runner_sha256
            receipt["resumed_after_core_replay"] = True
            raw_path = Path(temporary) / "raw-receipt.json"
            raw_path.write_text(json.dumps(receipt), encoding="ascii")
            raw_sha256 = hashlib.sha256(raw_path.read_bytes()).hexdigest()
            clean_start_markers = [
                "E058-CERTIFICATE-REGENERATION-PASS certificates=3",
                "Build completed successfully (1315 jobs).",
                (
                    "E058-RUP-CORES-PASS cores=89 c_checks=89 "
                    "python_checks=89 negative_checks=356 zero_rat=89"
                ),
            ]
            transcript_path = Path(temporary) / "audit.log"
            transcript_path.write_text(
                "\n".join(clean_start_markers)
                + "\nE058-FRESH-AUDIT-RESUME phase=test\n"
                + "E058-FRESH-LEAN-AUDIT-PASS "
                f"receipt_sha256={raw_sha256}\n",
                encoding="ascii",
            )
            sequence_receipt = {
                "verification": "CLEAN-START-SEQUENCE-PROVENANCE",
                "complete": True,
                "fresh_local_build": True,
                "resumed_after_core_replay": True,
                "clean_start_markers": clean_start_markers,
                "resume_segments": 1,
                "proof_counts": {
                    "cores": 89,
                    "kernel_imports": 89,
                    "semantic_closures": 89,
                    "axiom_queries": 192,
                },
                "axiom_queries": receipt["axiom_queries"],
                "warnings": 0,
                "forbidden_source_hits": 0,
                "source_inventory": receipt["source_inventory"],
                "transcript": {
                    "path": transcript_path.name,
                    "bytes": transcript_path.stat().st_size,
                    "sha256": hashlib.sha256(
                        transcript_path.read_bytes()
                    ).hexdigest(),
                },
                "raw_audit_receipt": {
                    "path": raw_path.name,
                    "bytes": raw_path.stat().st_size,
                    "sha256": raw_sha256,
                },
                "audit_runner": {
                    "path": runner_path.name,
                    "bytes": runner_path.stat().st_size,
                    "sha256_at_start": runner_sha256,
                    "binding": "SELF-HASHED-RUNNER-RECEIPT",
                },
            }
            path.write_text(json.dumps(sequence_receipt), encoding="ascii")
            sequence_observed = validate_clean_start_receipt(path)
            self.assertEqual(
                sequence_observed["verification"],
                "CLEAN-START-SEQUENCE-PROVENANCE",
            )
            sequence_receipt["resumed_after_core_replay"] = False
            path.write_text(json.dumps(sequence_receipt), encoding="ascii")
            with self.assertRaisesRegex(AuditError, "wrong scope"):
                validate_clean_start_receipt(path)

    def test_unit_validation_hashes_generated_and_committed_files(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repository = Path(temporary)
            generated_unit = repository / "work/unit.cnf"
            committed_unit = repository / "artifacts/unit.cnf"
            generated_unit.parent.mkdir(parents=True)
            committed_unit.parent.mkdir(parents=True)
            body = b"p cnf 1 1\n1 0\n"
            generated_unit.write_bytes(body)
            committed_unit.write_bytes(body)
            digest = hashlib.sha256(body).hexdigest()

            common = {
                "label": "sample",
                "source_raw_sha256": "0" * 64,
                "source_variables": 1,
                "source_clauses": 1,
                "unit_count": 1,
                "positive_units": 1,
                "negative_units": 0,
                "unit_cnf_bytes": len(body),
                "unit_cnf_sha256": digest,
            }
            generated_manifest = repository / "generated.json"
            expected_manifest = repository / "expected.json"
            generated_manifest.write_text(
                json.dumps(
                    {
                        "records": [
                            {
                                **common,
                                "unit_cnf": "work/unit.cnf",
                            }
                        ]
                    }
                ),
                encoding="ascii",
            )
            expected_manifest.write_text(
                json.dumps(
                    {
                        "records": [
                            {
                                **common,
                                "unit_cnf": "artifacts/unit.cnf",
                            }
                        ]
                    }
                ),
                encoding="ascii",
            )

            validate_unit_manifest(
                generated_manifest,
                expected_manifest,
                {"sample"},
                repository,
            )
            committed_unit.write_bytes(body.replace(b"1 0", b"-1 0"))
            with self.assertRaisesRegex(
                AuditError,
                "committed unit CNF mismatch",
            ):
                validate_unit_manifest(
                    generated_manifest,
                    expected_manifest,
                    {"sample"},
                    repository,
                )


if __name__ == "__main__":
    unittest.main()

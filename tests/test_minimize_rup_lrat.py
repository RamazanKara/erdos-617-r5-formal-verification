#!/usr/bin/env python3
"""Semantic, determinism, parser, and corruption tests for RUP core slicing."""

from __future__ import annotations

import json
import lzma
import sys
import tempfile
import unittest
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY))

from src.check_lrat import CheckError, check_lrat  # noqa: E402
from src.minimize_rup_lrat import MinimizeError, minimize  # noqa: E402
from repro.generate_e058_rup_cores import corruptions  # noqa: E402


CNF = """c deliberately contains one unreachable original clause
p cnf 2 5
1 2 0
-1 2 0
1 -2 0
-1 -2 0
1 0
"""

LRAT = """5 d 5 0
6 2 0 1 2 0
7 -2 0 4 3 0
7 d 6 0
8 1 0 7 1 0
9 0 7 2 8 0
"""

EXPECTED_CNF = """p cnf 2 4
1 2 0
-1 2 0
1 -2 0
-1 -2 0
"""

EXPECTED_LRAT = """5 -2 0 4 3 0
5 d 3 4 0
6 1 0 5 1 0
6 d 1 0
7 0 5 2 6 0
"""


def run_minimize(directory: Path, cnf: Path, proof: Path, stem: str = "core"):
    output_cnf = directory / f"{stem}.cnf"
    output_proof = directory / f"{stem}.lrat"
    map_path = directory / f"{stem}-map.json"
    receipt_path = directory / f"{stem}-receipt.json"
    receipt = minimize(
        source_cnf=cnf,
        source_proof=proof,
        output_cnf=output_cnf,
        output_proof=output_proof,
        map_path=map_path,
        receipt_path=receipt_path,
    )
    return output_cnf, output_proof, map_path, receipt_path, receipt


class MinimizeRupLratTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="erdos617-rup-core-")
        self.directory = Path(self.temporary.name)
        self.cnf = self.directory / "source.cnf"
        self.proof = self.directory / "source.lrat"
        self.cnf.write_text(CNF, encoding="ascii", newline="\n")
        self.proof.write_text(LRAT, encoding="ascii", newline="\n")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_exact_backward_core_and_external_semantics(self) -> None:
        originals, additions, _ = check_lrat(self.cnf, self.proof)
        self.assertEqual((originals, additions), (5, 4))

        output_cnf, output_proof, map_path, _, receipt = run_minimize(
            self.directory, self.cnf, self.proof
        )
        self.assertEqual(output_cnf.read_text(encoding="ascii"), EXPECTED_CNF)
        self.assertEqual(output_proof.read_text(encoding="ascii"), EXPECTED_LRAT)
        self.assertEqual(check_lrat(output_cnf, output_proof)[:2], (4, 3))

        mapping = json.loads(map_path.read_text(encoding="utf-8"))
        self.assertEqual(mapping["original_clause_ids"], [1, 2, 3, 4])
        self.assertEqual(mapping["derived_clause_ids"], [7, 8, 9])
        self.assertEqual(
            mapping["old_to_new"],
            {"1": 1, "2": 2, "3": 3, "4": 4, "7": 5, "8": 6, "9": 7},
        )
        self.assertEqual(receipt["core"]["rat_additions"], 0)
        self.assertEqual(receipt["core"]["original_clauses"], 4)
        self.assertEqual(receipt["core"]["additions"], 3)
        self.assertEqual(receipt["core"]["deleted_clauses"], 3)

    def test_xz_inputs_and_deterministic_outputs(self) -> None:
        cnf_xz = self.directory / "source.cnf.xz"
        proof_xz = self.directory / "source.lrat.xz"
        cnf_xz.write_bytes(lzma.compress(CNF.encode("ascii")))
        proof_xz.write_bytes(lzma.compress(LRAT.encode("ascii")))
        first = run_minimize(self.directory, cnf_xz, proof_xz, "first")
        second = run_minimize(self.directory, cnf_xz, proof_xz, "second")
        for first_path, second_path in zip(first[:3], second[:3], strict=True):
            self.assertEqual(first_path.read_bytes(), second_path.read_bytes())
        self.assertEqual(first[4]["source"]["cnf_raw_bytes"], len(CNF.encode("ascii")))
        self.assertEqual(first[4]["source"]["proof_raw_bytes"], len(LRAT.encode("ascii")))

    def test_truncated_and_forged_empty_proofs_are_rejected(self) -> None:
        output_cnf, output_proof, _, _, _ = run_minimize(
            self.directory, self.cnf, self.proof
        )
        lines = output_proof.read_text(encoding="ascii").splitlines(keepends=True)
        truncated = self.directory / "truncated.lrat"
        truncated.write_text("".join(lines[:-1]), encoding="ascii", newline="\n")
        forged = self.directory / "forged.lrat"
        forged.write_text("".join(lines[:-1]) + "7 0 1 0\n", encoding="ascii", newline="\n")
        with self.assertRaises(CheckError):
            check_lrat(output_cnf, truncated)
        with self.assertRaises(CheckError):
            check_lrat(output_cnf, forged)

    def test_invalid_proof_classes_are_rejected(self) -> None:
        cases = {
            "negative-hint": LRAT.replace("9 0 7 2 8 0", "9 0 -7 2 8 0"),
            "missing-hint": LRAT.replace("9 0 7 2 8 0", "9 0 99 2 8 0"),
            "missing-empty": LRAT.rsplit("9 0 7 2 8 0\n", 1)[0],
            "nonincreasing": LRAT.replace("8 1 0 7 1 0", "7 1 0 7 1 0"),
            "after-empty": LRAT + "10 1 0 1 2 0\n",
            "bad-deletion-label": LRAT.replace("7 d 6 0", "6 d 6 0"),
            "trailing-token": LRAT.replace("8 1 0 7 1 0", "8 1 0 7 1 0 4"),
        }
        for name, proof_text in cases.items():
            with self.subTest(name=name):
                bad_proof = self.directory / f"{name}.lrat"
                bad_proof.write_text(proof_text, encoding="ascii", newline="\n")
                with self.assertRaises(MinimizeError):
                    run_minimize(self.directory, self.cnf, bad_proof, name)

    def test_invalid_cnf_is_rejected(self) -> None:
        bad_cnf = self.directory / "bad.cnf"
        bad_cnf.write_text(CNF.replace("1 2 0", "1 1 0", 1), encoding="ascii", newline="\n")
        with self.assertRaises(MinimizeError):
            run_minimize(self.directory, bad_cnf, self.proof, "bad-cnf")

    def test_single_record_proof_corruptions(self) -> None:
        single = self.directory / "single.lrat"
        single.write_text("5 0 1 2 0\n", encoding="ascii", newline="\n")
        truncated, forged = corruptions(single, self.directory)
        self.assertEqual(truncated.read_bytes(), b"")
        self.assertEqual(forged.read_text(encoding="ascii"), "5 0 1 0\n")


if __name__ == "__main__":
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(MinimizeRupLratTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if result.wasSuccessful():
        print(
            "RUP-CORE-TEST-PASS cases=6 parser_rejections=8 "
            "external_corruptions=2 deterministic_runs=2"
        )
    raise SystemExit(not result.wasSuccessful())

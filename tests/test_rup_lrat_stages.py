from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from repro.generate_e058_lean_stage_modules import generate_modules
from repro.run_e058_lean_kernel_imports import (
    KernelImportError,
    replay_modules,
    replay_stages,
)
from src.split_rup_lrat_stages import SplitError, split_proof


CNF = """p cnf 2 4
1 2 0
-1 2 0
1 -2 0
-1 -2 0
"""

LRAT = """5 -2 0 4 3 0
5 d 3 4 0
6 1 0 5 1 0
6 d 1 0
7 0 5 2 6 0
"""


class RupLratStageTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="erdos617-rup-stages-")
        self.root = Path(self.temporary.name)
        self.cnf = self.root / "core.cnf"
        self.proof = self.root / "core.lrat"
        self.cnf.write_text(CNF, encoding="ascii", newline="\n")
        self.proof.write_text(LRAT, encoding="ascii", newline="\n")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_exact_boundaries_frontiers_and_determinism(self) -> None:
        first = self.root / "first"
        second = self.root / "second"
        receipt = split_proof(
            cnf_path=self.cnf,
            proof_path=self.proof,
            output_directory=first,
            stage_size=1,
        )
        split_proof(
            cnf_path=self.cnf,
            proof_path=self.proof,
            output_directory=second,
            stage_size=1,
        )
        self.assertEqual(receipt["total_additions"], 3)
        self.assertEqual([item["additions"] for item in receipt["stages"]], [1, 1, 1])
        self.assertEqual([item["final"] for item in receipt["stages"]], [False, False, True])
        self.assertEqual(
            (first / "stage_000.frontier").read_text(encoding="ascii"),
            "1 1 2 0\n2 -1 2 0\n5 -2 0\n",
        )
        self.assertEqual(
            (first / "stage_001.frontier").read_text(encoding="ascii"),
            "2 -1 2 0\n5 -2 0\n6 1 0\n",
        )
        self.assertEqual(
            (first / "stage_002.frontier").read_text(encoding="ascii"),
            "2 -1 2 0\n5 -2 0\n6 1 0\n7 0\n",
        )
        reconstructed = "".join(
            (first / f"stage_{index:03d}.lrat").read_text(encoding="ascii")
            for index in range(3)
        )
        self.assertEqual(reconstructed, LRAT)
        for index in range(3):
            for suffix in ("lrat", "frontier"):
                self.assertEqual(
                    (first / f"stage_{index:03d}.{suffix}").read_bytes(),
                    (second / f"stage_{index:03d}.{suffix}").read_bytes(),
                )

    def test_non_live_hints_and_deletions_are_rejected(self) -> None:
        cases = {
            "hint": LRAT.replace("6 1 0 5 1 0", "6 1 0 5 3 0"),
            "deletion": LRAT.replace("6 d 1 0", "6 d 3 0"),
        }
        for name, proof in cases.items():
            with self.subTest(name=name):
                path = self.root / f"{name}.lrat"
                path.write_text(proof, encoding="ascii", newline="\n")
                with self.assertRaises(SplitError):
                    split_proof(
                        cnf_path=self.cnf,
                        proof_path=path,
                        output_directory=self.root / f"out-{name}",
                        stage_size=1,
                    )
        with self.assertRaises(SplitError):
            split_proof(
                cnf_path=self.cnf,
                proof_path=self.proof,
                output_directory=self.root / "out-zero",
                stage_size=0,
            )

    def test_multi_stage_module_chain(self) -> None:
        stages = self.root / "multi-stages"
        split_proof(
            cnf_path=self.cnf,
            proof_path=self.proof,
            output_directory=stages,
            stage_size=1,
        )
        modules = self.root / "multi-modules"
        receipt = generate_modules(
            stage_directory=stages,
            cnf_path=self.cnf,
            output_directory=modules,
            module_prefix="E058TestMulti",
            importer_module="Erdos617.Sat.LRATStage",
        )
        self.assertEqual(len(receipt["modules"]), 3)
        first = (modules / "E058TestMultiStage000.lean").read_text(encoding="ascii")
        middle = (modules / "E058TestMultiStage001.lean").read_text(encoding="ascii")
        final = (modules / "E058TestMultiStage002.lean").read_text(encoding="ascii")
        self.assertIn("lrat_stage_initial_file E058TestMultiStage000", first)
        self.assertIn("import E058TestMultiStage000", middle)
        self.assertIn("lrat_stage_continue_file E058TestMultiStage001", middle)
        self.assertIn("lrat_stage_final_file E058TestMultiKernelProof", final)
        self.assertIn("#print axioms E058TestMultiKernelProof", final)

    def test_single_stage_module(self) -> None:
        stages = self.root / "single-stages"
        split_proof(
            cnf_path=self.cnf,
            proof_path=self.proof,
            output_directory=stages,
            stage_size=10,
        )
        modules = self.root / "single-modules"
        receipt = generate_modules(
            stage_directory=stages,
            cnf_path=self.cnf,
            output_directory=modules,
            module_prefix="E058TestSingle",
            importer_module="Erdos617.Sat.LRATStage",
            path_root=self.root,
        )
        self.assertEqual(len(receipt["modules"]), 1)
        source = (modules / "E058TestSingleStage000.lean").read_text(encoding="ascii")
        self.assertIn("lrat_stage_initial_final_file E058TestSingleKernelProof", source)
        self.assertNotIn("lrat_stage_initial_file E058TestSingleStage000", source)
        self.assertIn('"core.cnf"', source)
        self.assertIn('"single-stages/stage_000.lrat"', source)
        self.assertNotIn(str(self.root), source)

    def test_committed_stage_source_is_replayed_before_reuse(self) -> None:
        work = self.root / "work"
        work.mkdir()
        stages = work / "stages"
        first = replay_stages(
            cnf=self.cnf,
            proof=self.proof,
            stages_directory=stages,
            core_work=work,
        )
        second = replay_stages(
            cnf=self.cnf,
            proof=self.proof,
            stages_directory=stages,
            core_work=work,
        )
        self.assertEqual(first, second)

        modules = self.root / "modules"
        with patch(
            "repro.run_e058_lean_kernel_imports.LEAN_ROOT",
            self.root,
        ):
            receipt, receipt_path = replay_modules(
                stages_directory=stages,
                cnf=self.cnf,
                modules_directory=modules,
                core_work=work,
                prefix="E058TestReplay",
            )
            self.assertTrue(receipt_path.is_file())
            replay_modules(
                stages_directory=stages,
                cnf=self.cnf,
                modules_directory=modules,
                core_work=work,
                prefix="E058TestReplay",
            )
            source = modules / str(receipt["modules"][0]["source"])
            source.write_text(
                source.read_text(encoding="ascii") + "\n",
                encoding="ascii",
            )
            with self.assertRaisesRegex(
                KernelImportError,
                "source replay differs",
            ):
                replay_modules(
                    stages_directory=stages,
                    cnf=self.cnf,
                    modules_directory=modules,
                    core_work=work,
                    prefix="E058TestReplay",
                )


if __name__ == "__main__":
    unittest.main(verbosity=2)

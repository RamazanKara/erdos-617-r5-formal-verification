from __future__ import annotations

import ast
import hashlib
import inspect
import tempfile
import unittest
from pathlib import Path

import repro.run_e058_lean_semantic_closures as semantic_runner
from repro.run_e058_lean_semantic_closures import (
    SemanticClosureError,
    comparison_scheme,
    read_dimacs_header,
    render_semantic_source,
    validate_axioms,
    validate_unit_cnf,
)


class LeanSemanticClosureRunnerTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(
            prefix="erdos617-semantic-closure-"
        )
        self.root = Path(self.temporary.name)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_full_exterior_source_is_exact(self) -> None:
        module, theorem, source = render_semantic_source(
            label="e038_branch_02",
            final_kernel_module="E058KernelE038Branch02Stage000",
            final_kernel_theorem="E058KernelE038Branch02KernelProof",
            kernel_context="E058KernelE038Branch02KernelProof.ctx",
            variable_count=3930,
            scheme="full_exterior",
            core_path=self.root / "core.cnf",
            unit_path=self.root / "units.cnf",
        )
        self.assertEqual(module, "E058SemanticE038Branch02Closure")
        self.assertEqual(theorem, "E058SemanticE038Branch02Contradiction")
        self.assertIn(
            "lrat_reify_stored E058SemanticE038Branch02Reified 3930", source
        )
        self.assertIn(
            "E058KernelE038Branch02KernelProof.ctx\n"
            "  E058KernelE038Branch02KernelProof",
            source,
        )
        self.assertIn(
            "full_exterior E058SemanticE038Branch02GraphFormula", source
        )
        self.assertIn(
            "#print axioms E058SemanticE038Branch02Contradiction", source
        )

    def test_zero_anchor_source_and_allocation_dispatch(self) -> None:
        _, _, source = render_semantic_source(
            label="e045_branch_25",
            final_kernel_module="E058KernelE045Branch25Stage000",
            final_kernel_theorem="E058KernelE045Branch25KernelProof",
            kernel_context="E058KernelE045Branch25KernelProof.ctx",
            variable_count=3920,
            scheme=comparison_scheme(3920),
            core_path=self.root / "core.cnf",
            unit_path=self.root / "units.cnf",
        )
        self.assertIn("zero_anchor E058SemanticE045Branch25Reified", source)
        self.assertEqual(comparison_scheme(3930), "full_exterior")
        with self.assertRaises(SemanticClosureError):
            comparison_scheme(3921)

    def test_multi_stage_context_is_rendered_verbatim(self) -> None:
        _, _, source = render_semantic_source(
            label="e038_branch_05",
            final_kernel_module="E058KernelE038Branch05Stage003",
            final_kernel_theorem="E058KernelE038Branch05KernelProof",
            kernel_context="E058KernelE038Branch05Stage000.ctx",
            variable_count=3930,
            scheme="full_exterior",
            core_path=self.root / "core.cnf",
            unit_path=self.root / "units.cnf",
        )
        self.assertIn(
            "E058KernelE038Branch05Stage000.ctx\n"
            "  E058KernelE038Branch05KernelProof",
            source,
        )

    def test_unit_cnf_validation(self) -> None:
        good = self.root / "good.cnf"
        good.write_text(
            "p cnf 3930 3\n1 0\n-2 0\n325 0\n",
            encoding="ascii",
            newline="\n",
        )
        self.assertEqual(read_dimacs_header(good), (3930, 3))
        self.assertEqual(validate_unit_cnf(good), (3930, [1, -2, 325]))
        for name, body in {
            "duplicate": "p cnf 3930 2\n1 0\n1 0\n",
            "contradiction": "p cnf 3930 2\n1 0\n-1 0\n",
            "auxiliary": "p cnf 3930 1\n326 0\n",
            "nonunit": "p cnf 3930 1\n1 2 0\n",
        }.items():
            with self.subTest(name=name):
                path = self.root / f"{name}.cnf"
                path.write_text(body, encoding="ascii", newline="\n")
                with self.assertRaises(SemanticClosureError):
                    validate_unit_cnf(path)

    def test_axiom_audit_is_exact(self) -> None:
        theorem = "E058SemanticTestContradiction"
        expected = (
            f"'{theorem}' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]"
        )
        self.assertEqual(validate_axioms(expected + "\n", theorem), expected)
        with self.assertRaises(SemanticClosureError):
            validate_axioms(
                f"'{theorem}' depends on axioms: [propext, sorryAx]\n",
                theorem,
            )
        main_source = inspect.getsource(semantic_runner.main)
        main_function = ast.parse(main_source).body[0]
        direct_result_assignments = [
            statement
            for statement in main_function.body
            if isinstance(statement, ast.Assign)
            and any(
                isinstance(target, ast.Name) and target.id == "result"
                for target in statement.targets
            )
        ]
        self.assertEqual(len(direct_result_assignments), 1)

        source_path = self.root / "generated/E058SemanticSampleClosure.lean"
        source_path.parent.mkdir(parents=True)
        source_path.write_text("-- generated closure\n", encoding="ascii")
        output_path = self.root / "E058SemanticSampleClosure.olean"
        output_path.write_bytes(b"olean")
        core_path = self.root / "sample.cnf"
        core_path.write_bytes(b"p cnf 1 1\n1 0\n")
        unit_path = self.root / "sample-units.cnf"
        unit_path.write_bytes(b"p cnf 1 1\n1 0\n")
        kernel_receipt_path = self.root / "kernel-receipt.json"
        kernel_receipt_path.write_text("{}\n", encoding="ascii")
        compile_log = self.root / "compile.log"
        audit_log = self.root / "audit.log"
        compile_log.write_text(expected + "\n", encoding="ascii")
        audit_log.write_text(expected + "\n", encoding="ascii")
        audit_path = (
            source_path.parent / "E058SemanticSampleClosureFreshAudit.lean"
        )
        audit_path.write_text(
            semantic_runner.fresh_audit_source(
                "E058SemanticSampleClosure",
                theorem,
            ),
            encoding="ascii",
        )

        def digest(path: Path) -> str:
            return hashlib.sha256(path.read_bytes()).hexdigest()

        kernel_olean_sha256 = "a" * 64
        verified = {
            "label": "sample",
            "scheme": "full_exterior",
            "core_variables": 1,
            "core_clauses": 1,
            "unit_count": 1,
            "final_kernel_theorem": "E058KernelSampleKernelProof",
            "final_kernel_module": "E058KernelSampleStage000",
            "kernel_context": "E058KernelSampleKernelProof.ctx",
            "kernel_receipt": {
                "final_olean": {"sha256": kernel_olean_sha256},
            },
        }
        receipt = {
            "verification": "LEAN-KERNEL-CONDITIONAL-GRAPH-UNSAT",
            "label": "sample",
            "comparison_scheme": "full_exterior",
            "theorem": theorem,
            "source": str(source_path),
            "source_sha256": digest(source_path),
            "core": {
                "path": str(core_path),
                "variables": 1,
                "clauses": 1,
                "sha256": digest(core_path),
            },
            "units": {
                "path": str(unit_path),
                "count": 1,
                "sha256": digest(unit_path),
            },
            "kernel_import": {
                "receipt": str(kernel_receipt_path),
                "receipt_sha256": digest(kernel_receipt_path),
                "theorem": "E058KernelSampleKernelProof",
                "module": "E058KernelSampleStage000",
                "context": "E058KernelSampleKernelProof.ctx",
                "olean_sha256": kernel_olean_sha256,
            },
            "olean": {
                "path": str(output_path),
                "bytes": output_path.stat().st_size,
                "sha256": digest(output_path),
            },
            "compile": {
                "axiom_audit": expected,
                "log": {
                    "path": str(compile_log),
                    "bytes": compile_log.stat().st_size,
                    "sha256": digest(compile_log),
                },
            },
            "fresh_audit": {
                "axiom_audit": expected,
                "log": {
                    "path": str(audit_log),
                    "bytes": audit_log.stat().st_size,
                    "sha256": digest(audit_log),
                },
            },
        }
        self.assertTrue(
            semantic_runner.completed_receipt_is_current(
                receipt,
                verified=verified,
                module_name="E058SemanticSampleClosure",
                theorem_name=theorem,
                source_path=source_path,
                output_path=output_path,
                core_path=core_path,
                unit_path=unit_path,
                kernel_receipt_path=kernel_receipt_path,
            )
        )
        output_path.write_bytes(b"tampered")
        self.assertFalse(
            semantic_runner.completed_receipt_is_current(
                receipt,
                verified=verified,
                module_name="E058SemanticSampleClosure",
                theorem_name=theorem,
                source_path=source_path,
                output_path=output_path,
                core_path=core_path,
                unit_path=unit_path,
                kernel_receipt_path=kernel_receipt_path,
            )
        )


if __name__ == "__main__":
    unittest.main(verbosity=2)

#!/usr/bin/env python3
"""Generate Lean source modules for a staged RUP kernel import."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path


class ModuleGenerationError(ValueError):
    """Raised when a stage receipt cannot define a deterministic module chain."""


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def lean_string(value: Path, path_root: Path | None) -> str:
    resolved = value.resolve()
    rendered = (
        Path(os.path.relpath(resolved, path_root.resolve()))
        if path_root is not None
        else resolved
    )
    return json.dumps(str(rendered))


def generate_modules(
    *,
    stage_directory: Path,
    cnf_path: Path,
    output_directory: Path,
    module_prefix: str,
    importer_module: str,
    path_root: Path | None = None,
) -> dict[str, object]:
    receipt_path = stage_directory / "receipt.json"
    receipt = json.loads(receipt_path.read_text(encoding="ascii"))
    stages = receipt.get("stages")
    if not isinstance(stages, list) or not stages:
        raise ModuleGenerationError("stage receipt has no stages")
    if [record.get("stage") for record in stages] != list(range(len(stages))):
        raise ModuleGenerationError("stage receipt numbering is not consecutive")
    if any(bool(record.get("final")) for record in stages[:-1]):
        raise ModuleGenerationError("nonterminal stage is marked final")
    if not bool(stages[-1].get("final")):
        raise ModuleGenerationError("terminal stage is not marked final")
    if not module_prefix or not all(part.isidentifier() for part in module_prefix.split(".")):
        raise ModuleGenerationError("module prefix is not a dotted identifier")
    if not importer_module or not all(
        part.isidentifier() for part in importer_module.split(".")
    ):
        raise ModuleGenerationError("importer module is not a dotted identifier")

    output_directory.mkdir(parents=True, exist_ok=True)
    targets = [output_directory / f"{module_prefix}Stage{index:03d}.lean" for index in range(len(stages))]
    collisions = [path for path in targets if path.exists()]
    if collisions:
        raise ModuleGenerationError(f"module target already exists: {collisions[0]}")

    generated: list[dict[str, object]] = []
    ctx_name = f"{module_prefix}Stage000.ctx"
    for index, record in enumerate(stages):
        module_name = f"{module_prefix}Stage{index:03d}"
        source_path = targets[index]
        chunk_path = stage_directory / record["chunk"]["path"]
        frontier_path = stage_directory / record["frontier"]["path"]
        if not chunk_path.is_file() or not frontier_path.is_file():
            raise ModuleGenerationError(f"missing stage artifact for stage {index}")
        if sha256_path(chunk_path) != record["chunk"]["sha256"]:
            raise ModuleGenerationError(f"chunk hash mismatch at stage {index}")
        if sha256_path(frontier_path) != record["frontier"]["sha256"]:
            raise ModuleGenerationError(f"frontier hash mismatch at stage {index}")

        if len(stages) == 1:
            theorem_name = f"{module_prefix}KernelProof"
            body = (
                f"import {importer_module}\n\n"
                "set_option maxHeartbeats 0 in\n"
                f"lrat_stage_initial_final_file {theorem_name}\n"
                f"  {lean_string(cnf_path, path_root)}\n"
                f"  {lean_string(chunk_path, path_root)}\n\n"
                f"#print axioms {theorem_name}\n"
            )
        elif index == 0:
            body = (
                f"import {importer_module}\n\n"
                "set_option maxHeartbeats 0 in\n"
                f"lrat_stage_initial_file {module_name}\n"
                f"  {lean_string(cnf_path, path_root)}\n"
                f"  {lean_string(chunk_path, path_root)}\n"
                f"  {lean_string(frontier_path, path_root)}\n\n"
                f"#print axioms {module_name}.frontier\n"
            )
        elif index + 1 == len(stages):
            prior_name = f"{module_prefix}Stage{index - 1:03d}"
            prior_frontier = stage_directory / stages[index - 1]["frontier"]["path"]
            theorem_name = f"{module_prefix}KernelProof"
            body = (
                f"import {prior_name}\n\n"
                "set_option maxHeartbeats 0 in\n"
                f"lrat_stage_final_file {theorem_name} {ctx_name} {prior_name}\n"
                f"  {lean_string(prior_frontier, path_root)}\n"
                f"  {lean_string(chunk_path, path_root)}\n\n"
                f"#print axioms {theorem_name}\n"
            )
        else:
            prior_name = f"{module_prefix}Stage{index - 1:03d}"
            prior_frontier = stage_directory / stages[index - 1]["frontier"]["path"]
            body = (
                f"import {prior_name}\n\n"
                "set_option maxHeartbeats 0 in\n"
                f"lrat_stage_continue_file {module_name} {ctx_name} {prior_name}\n"
                f"  {lean_string(prior_frontier, path_root)}\n"
                f"  {lean_string(chunk_path, path_root)}\n"
                f"  {lean_string(frontier_path, path_root)}\n\n"
                f"#print axioms {module_name}.frontier\n"
            )
        source_path.write_text(body, encoding="ascii", newline="\n")
        generated.append(
            {
                "stage": index,
                "module": module_name,
                "source": source_path.name,
                "bytes": source_path.stat().st_size,
                "sha256": sha256_path(source_path),
            }
        )

    module_receipt: dict[str, object] = {
        "schema_version": 1,
        "module_prefix": module_prefix,
        "importer_module": importer_module,
        "stage_receipt": {
            "path": str(receipt_path.resolve()),
            "sha256": sha256_path(receipt_path),
        },
        "cnf": {"path": str(cnf_path.resolve()), "sha256": sha256_path(cnf_path)},
        "modules": generated,
        "final_theorem": f"{module_prefix}KernelProof",
    }
    output_receipt = output_directory / "lean-stage-modules-receipt.json"
    if output_receipt.exists():
        raise ModuleGenerationError(f"module receipt already exists: {output_receipt}")
    output_receipt.write_text(
        json.dumps(module_receipt, indent=2, sort_keys=True) + "\n", encoding="ascii"
    )
    return module_receipt


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--stage-directory", type=Path, required=True)
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--output-directory", type=Path, required=True)
    parser.add_argument("--module-prefix", required=True)
    parser.add_argument("--importer-module", default="Erdos617.Sat.LRATStage")
    parser.add_argument("--path-root", type=Path)
    args = parser.parse_args()
    try:
        receipt = generate_modules(
            stage_directory=args.stage_directory.resolve(),
            cnf_path=args.cnf.resolve(),
            output_directory=args.output_directory.resolve(),
            module_prefix=args.module_prefix,
            importer_module=args.importer_module,
            path_root=args.path_root.resolve() if args.path_root else None,
        )
    except (KeyError, OSError, TypeError, json.JSONDecodeError, ModuleGenerationError) as error:
        raise SystemExit(f"LEAN-STAGE-MODULE-GENERATION-FAILED: {error}") from error
    print(
        "LEAN-STAGE-MODULE-GENERATION-PASS "
        f"modules={len(receipt['modules'])} final={receipt['final_theorem']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

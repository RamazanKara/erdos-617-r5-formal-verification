#!/usr/bin/env python3
"""Build, hash, and freshly audit staged Lean imports for E058 RUP cores."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
LEAN_ROOT = REPOSITORY / "formal/lean"
LEAN_BIN = Path(
    os.environ.get(
        "E058_LEAN_LAKE",
        Path.home() / ".elan/toolchains/leanprover--lean4---v4.32.0/bin/lake",
    )
)
sys.path.insert(0, str(REPOSITORY))

from repro.generate_e058_lean_stage_modules import generate_modules  # noqa: E402
from src.split_rup_lrat_stages import split_proof  # noqa: E402


class KernelImportError(RuntimeError):
    """Raised when a staged Lean kernel import fails an exact audit gate."""


RESOURCE_PATTERN = re.compile(
    r"E058_RESOURCE wall=(?P<wall>[0-9.]+) max_rss_kb=(?P<rss>[0-9]+) exit=(?P<exit>[0-9]+)"
)


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="ascii")


def module_prefix(label: str) -> str:
    parts = label.split("_")
    if not parts or any(not part.isalnum() for part in parts):
        raise KernelImportError(f"unsupported core label: {label}")
    return "E058Kernel" + "".join(part[:1].upper() + part[1:] for part in parts)


def run_lean(
    *, source: Path, output: Path | None, timeout_seconds: int, log_path: Path
) -> dict[str, object]:
    command = [
        "/usr/bin/time",
        "-f",
        "E058_RESOURCE wall=%e max_rss_kb=%M exit=%x",
        str(LEAN_BIN),
        "env",
        "lean",
        "-j1",
        "-M8192",
    ]
    if output is not None:
        command.extend(["-o", str(output)])
    command.append(str(source))
    started = time.monotonic()
    try:
        result = subprocess.run(
            command,
            cwd=LEAN_ROOT,
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired as error:
        raise KernelImportError(f"Lean timeout for {source.name}") from error
    combined = result.stdout + result.stderr
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(combined, encoding="utf-8", newline="\n")
    if result.returncode != 0:
        raise KernelImportError(
            f"Lean failed for {source.name} with {result.returncode}; see {log_path}"
        )
    matches = list(RESOURCE_PATTERN.finditer(combined))
    if len(matches) != 1 or int(matches[0].group("exit")) != 0:
        raise KernelImportError(f"missing successful resource record for {source.name}")
    return {
        "command": command,
        "wall_seconds": float(matches[0].group("wall")),
        "max_rss_kb": int(matches[0].group("rss")),
        "elapsed_observed_seconds": time.monotonic() - started,
        "log": {
            "path": str(log_path),
            "bytes": log_path.stat().st_size,
            "sha256": sha256_path(log_path),
        },
        "output": combined,
    }


def expected_axiom_subject(prefix: str, stage: int, stage_count: int) -> str:
    if stage + 1 == stage_count:
        return f"{prefix}KernelProof"
    return f"{prefix}Stage{stage:03d}.frontier"


def validate_axioms(output: str, subject: str) -> str:
    expected = f"'{subject}' depends on axioms: [propext]"
    lines = [line.strip() for line in output.splitlines() if "depends on axioms:" in line]
    if lines != [expected]:
        raise KernelImportError(f"axiom audit mismatch for {subject}: {lines}")
    return expected


def verify_core_inputs(core_directory: Path, record: dict[str, object]) -> tuple[Path, Path]:
    core = record["core"]
    cnf = core_directory / core["cnf_path"]
    proof = core_directory / core["proof_path"]
    if sha256_path(cnf) != core["cnf_sha256"]:
        raise KernelImportError(f"CNF hash mismatch for {record['label']}")
    if sha256_path(proof) != core["proof_sha256"]:
        raise KernelImportError(f"proof hash mismatch for {record['label']}")
    return cnf, proof


def fresh_audit_source(module_name: str, theorem_name: str) -> str:
    return (
        f"import {module_name}\n\n"
        f"#check {theorem_name}\n"
        f"#print axioms {theorem_name}\n"
    )


def replay_stages(
    *,
    cnf: Path,
    proof: Path,
    stages_directory: Path,
    core_work: Path,
) -> dict[str, object]:
    receipt_path = stages_directory / "receipt.json"
    if not receipt_path.is_file():
        if stages_directory.exists() and any(stages_directory.iterdir()):
            raise KernelImportError(
                f"incomplete stage directory: {stages_directory}"
            )
        return split_proof(
            cnf_path=cnf,
            proof_path=proof,
            output_directory=stages_directory,
            stage_size=10_000,
        )

    receipt = json.loads(receipt_path.read_text(encoding="ascii"))
    with tempfile.TemporaryDirectory(
        prefix="stage-replay-", dir=core_work
    ) as temporary:
        replay_directory = Path(temporary)
        replay = split_proof(
            cnf_path=cnf,
            proof_path=proof,
            output_directory=replay_directory,
            stage_size=10_000,
        )
        if replay != receipt:
            raise KernelImportError(
                f"stage replay receipt differs: {stages_directory}"
            )
        for record in replay["stages"]:
            for kind in ("chunk", "frontier"):
                relative = Path(str(record[kind]["path"]))
                expected = replay_directory / relative
                observed = stages_directory / relative
                if (
                    not observed.is_file()
                    or observed.read_bytes() != expected.read_bytes()
                ):
                    raise KernelImportError(
                        f"stage replay bytes differ: {observed}"
                    )
    return receipt


def replay_modules(
    *,
    stages_directory: Path,
    cnf: Path,
    modules_directory: Path,
    core_work: Path,
    prefix: str,
) -> tuple[dict[str, object], Path]:
    modules_directory.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix="module-replay-", dir=core_work
    ) as temporary:
        replay_directory = Path(temporary)
        replay = generate_modules(
            stage_directory=stages_directory,
            cnf_path=cnf,
            output_directory=replay_directory,
            module_prefix=prefix,
            importer_module="Erdos617.Sat.LRATStage",
            path_root=LEAN_ROOT,
        )
        expected_sources = {
            str(module["source"]): replay_directory / str(module["source"])
            for module in replay["modules"]
        }
        observed_stage_sources = {
            path.name: path
            for path in modules_directory.glob(f"{prefix}Stage*.lean")
        }
        unexpected = sorted(set(observed_stage_sources) - set(expected_sources))
        if unexpected:
            raise KernelImportError(
                f"unexpected generated stage sources for {prefix}: {unexpected}"
            )
        if observed_stage_sources:
            missing = sorted(set(expected_sources) - set(observed_stage_sources))
            if missing:
                raise KernelImportError(
                    f"incomplete generated stage sources for {prefix}: {missing}"
                )
            for name, expected in expected_sources.items():
                if observed_stage_sources[name].read_bytes() != expected.read_bytes():
                    raise KernelImportError(
                        f"generated stage source replay differs: "
                        f"{observed_stage_sources[name]}"
                    )
        else:
            for name, expected in expected_sources.items():
                shutil.copyfile(expected, modules_directory / name)

        receipt_path = modules_directory / "lean-stage-modules-receipt.json"
        shutil.copyfile(
            replay_directory / "lean-stage-modules-receipt.json",
            receipt_path,
        )
    return replay, receipt_path


def validate_completed_receipt(
    *,
    receipt: dict[str, object],
    record: dict[str, object],
    prefix: str,
    stages_directory: Path,
    modules_directory: Path,
    stage_receipt: dict[str, object],
    module_receipt: dict[str, object],
    module_receipt_path: Path,
) -> None:
    label = str(record["label"])
    modules = module_receipt.get("modules")
    compiled = receipt.get("compiled_stages")
    final_theorem = prefix + "KernelProof"
    if (
        receipt.get("verification") != "LEAN-KERNEL-RUP-UNSAT"
        or receipt.get("label") != label
        or receipt.get("core") != record["core"]
        or receipt.get("final_theorem") != final_theorem
        or not isinstance(modules, list)
        or not isinstance(compiled, list)
        or len(modules) == 0
        or len(compiled) != len(modules)
        or receipt.get("stage_count") != len(modules)
        or receipt.get("module_receipt_sha256")
        != sha256_path(module_receipt_path)
        or receipt.get("stages_receipt_sha256")
        != sha256_path(stages_directory / "receipt.json")
        or receipt.get("stage_additions")
        != [stage["additions"] for stage in stage_receipt["stages"]]
    ):
        raise KernelImportError(f"stale completed receipt for {label}")

    for index, (module, stage) in enumerate(zip(modules, compiled, strict=True)):
        source = modules_directory / str(module["source"])
        olean = Path(str(stage["olean_path"]))
        log = Path(str(stage["log"]["path"]))
        expected_axiom = (
            f"'{expected_axiom_subject(prefix, index, len(modules))}' "
            "depends on axioms: [propext]"
        )
        if (
            module.get("stage") != index
            or stage.get("stage") != index
            or stage.get("module") != module.get("module")
            or not source.is_file()
            or source.stat().st_size != module.get("bytes")
            or sha256_path(source) != module.get("sha256")
            or stage.get("source_sha256") != module.get("sha256")
            or not olean.is_file()
            or olean.stat().st_size != stage.get("olean_bytes")
            or sha256_path(olean) != stage.get("olean_sha256")
            or stage.get("axiom_audit") != expected_axiom
            or not log.is_file()
            or log.stat().st_size != stage["log"].get("bytes")
            or sha256_path(log) != stage["log"].get("sha256")
        ):
            raise KernelImportError(
                f"stale completed receipt for {label} stage {index}"
            )

    final_stage = compiled[-1]
    final_olean = Path(str(receipt["final_olean"]["path"]))
    audit_source = modules_directory / f"{prefix}FreshAudit.lean"
    audit_log = Path(str(receipt["fresh_audit"]["log"]["path"]))
    expected_audit = fresh_audit_source(str(modules[-1]["module"]), final_theorem)
    expected_axiom = f"'{final_theorem}' depends on axioms: [propext]"
    if (
        receipt["final_olean"].get("sha256") != final_stage.get("olean_sha256")
        or receipt["final_olean"].get("bytes") != final_stage.get("olean_bytes")
        or not final_olean.is_file()
        or sha256_path(final_olean) != receipt["final_olean"].get("sha256")
        or not audit_source.is_file()
        or audit_source.read_text(encoding="ascii") != expected_audit
        or receipt["fresh_audit"].get("axiom_audit") != expected_axiom
        or not audit_log.is_file()
        or audit_log.stat().st_size != receipt["fresh_audit"]["log"].get("bytes")
        or sha256_path(audit_log)
        != receipt["fresh_audit"]["log"].get("sha256")
    ):
        raise KernelImportError(f"stale completed receipt for {label}")


def compile_core(
    *,
    core_directory: Path,
    record: dict[str, object],
    work_directory: Path,
    source_directory: Path,
    timeout_seconds: int,
) -> dict[str, object]:
    label = str(record["label"])
    prefix = module_prefix(label)
    core_work = work_directory / label
    stages_directory = core_work / "stages"
    modules_directory = source_directory / label
    logs_directory = core_work / "logs"
    progress_path = core_work / "progress.json"
    final_receipt_path = core_work / "kernel-receipt.json"
    cnf, proof = verify_core_inputs(core_directory, record)

    core_work.mkdir(parents=True, exist_ok=True)
    stage_receipt = replay_stages(
        cnf=cnf,
        proof=proof,
        stages_directory=stages_directory,
        core_work=core_work,
    )
    module_receipt, module_receipt_path = replay_modules(
        stages_directory=stages_directory,
        cnf=cnf,
        modules_directory=modules_directory,
        core_work=core_work,
        prefix=prefix,
    )

    if final_receipt_path.is_file():
        final_receipt = json.loads(final_receipt_path.read_text(encoding="ascii"))
        validate_completed_receipt(
            receipt=final_receipt,
            record=record,
            prefix=prefix,
            stages_directory=stages_directory,
            modules_directory=modules_directory,
            stage_receipt=stage_receipt,
            module_receipt=module_receipt,
            module_receipt_path=module_receipt_path,
        )
        print(
            f"E058-KERNEL-CORE-SKIP label={label} reason=verified-receipt",
            flush=True,
        )
        return final_receipt

    progress: dict[str, object]
    if progress_path.is_file():
        progress = json.loads(progress_path.read_text(encoding="ascii"))
    else:
        progress = {
            "schema_version": 1,
            "label": label,
            "prefix": prefix,
            "core_cnf_sha256": sha256_path(cnf),
            "core_proof_sha256": sha256_path(proof),
            "stages": [],
        }
    completed = progress["stages"]
    if not isinstance(completed, list):
        raise KernelImportError(f"bad progress receipt for {label}")

    stage_count = len(module_receipt["modules"])
    for stage, module in enumerate(module_receipt["modules"]):
        module_name = str(module["module"])
        source = modules_directory / module["source"]
        output = LEAN_ROOT / ".lake/build/lib/lean" / f"{module_name}.olean"
        if stage < len(completed):
            prior = completed[stage]
            if prior["module"] != module_name:
                raise KernelImportError(f"progress module mismatch for {label} stage {stage}")
            if not output.is_file() or sha256_path(output) != prior["olean_sha256"]:
                raise KernelImportError(f"stale stage artifact for {label} stage {stage}")
            continue
        print(
            f"E058-KERNEL-STAGE-START label={label} stage={stage + 1}/{stage_count}",
            flush=True,
        )
        run = run_lean(
            source=source,
            output=output,
            timeout_seconds=timeout_seconds,
            log_path=logs_directory / f"stage_{stage:03d}.log",
        )
        subject = expected_axiom_subject(prefix, stage, stage_count)
        axiom_line = validate_axioms(str(run.pop("output")), subject)
        stage_record = {
            "stage": stage,
            "module": module_name,
            "source_sha256": sha256_path(source),
            "olean_path": str(output),
            "olean_bytes": output.stat().st_size,
            "olean_sha256": sha256_path(output),
            "axiom_audit": axiom_line,
            **run,
        }
        completed.append(stage_record)
        write_json(progress_path, progress)
        print(
            f"E058-KERNEL-STAGE-PASS label={label} stage={stage + 1}/{stage_count} "
            f"wall={stage_record['wall_seconds']} max_rss_kb={stage_record['max_rss_kb']}",
            flush=True,
        )

    final_module = str(module_receipt["modules"][-1]["module"])
    final_theorem = str(module_receipt["final_theorem"])
    audit_source = modules_directory / f"{prefix}FreshAudit.lean"
    audit_source.write_text(
        fresh_audit_source(final_module, final_theorem), encoding="ascii", newline="\n"
    )
    audit_run = run_lean(
        source=audit_source,
        output=None,
        timeout_seconds=timeout_seconds,
        log_path=logs_directory / "fresh-audit.log",
    )
    audit_output = str(audit_run.pop("output"))
    audit_axiom = validate_axioms(audit_output, final_theorem)
    if f"{final_theorem} :" not in audit_output or ".proof Sat.Clause.nil" not in audit_output:
        raise KernelImportError(f"fresh theorem type audit mismatch for {label}")
    final_stage = completed[-1]
    final_receipt: dict[str, object] = {
        "schema_version": 1,
        "experiment": "E058-R5-SPECIAL-BROOKS-KERNEL-BRIDGE",
        "label": label,
        "verification": "LEAN-KERNEL-RUP-UNSAT",
        "core": record["core"],
        "stage_count": stage_count,
        "stage_additions": [stage["additions"] for stage in stage_receipt["stages"]],
        "module_receipt_sha256": sha256_path(module_receipt_path),
        "stages_receipt_sha256": sha256_path(stages_directory / "receipt.json"),
        "compiled_stages": completed,
        "final_theorem": final_theorem,
        "final_olean": {
            "path": final_stage["olean_path"],
            "bytes": final_stage["olean_bytes"],
            "sha256": final_stage["olean_sha256"],
        },
        "fresh_audit": {"axiom_audit": audit_axiom, **audit_run},
    }
    write_json(final_receipt_path, final_receipt)
    print(
        f"E058-KERNEL-CORE-PASS label={label} stages={stage_count} "
        f"additions={record['core']['additions']} theorem={final_theorem}",
        flush=True,
    )
    return final_receipt


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--core-directory", type=Path, required=True)
    parser.add_argument("--work-directory", type=Path, required=True)
    parser.add_argument("--source-directory", type=Path, required=True)
    parser.add_argument("--only", action="append", default=[])
    parser.add_argument("--timeout-seconds", type=int, default=1200)
    args = parser.parse_args()
    core_directory = args.core_directory.resolve()
    work_directory = args.work_directory.resolve()
    source_directory = args.source_directory.resolve()
    try:
        source_directory.relative_to(LEAN_ROOT.resolve())
    except ValueError as error:
        raise SystemExit("source directory must be inside the Lean package root") from error
    aggregate_source = core_directory / "receipt.json"
    aggregate = json.loads(aggregate_source.read_text(encoding="ascii"))
    records = aggregate["records"]
    selected = set(args.only)
    if selected:
        known = {record["label"] for record in records}
        unknown = selected - known
        if unknown:
            raise SystemExit(f"unknown --only labels: {sorted(unknown)}")
        records = [record for record in records if record["label"] in selected]
    work_directory.mkdir(parents=True, exist_ok=True)
    source_directory.mkdir(parents=True, exist_ok=True)
    receipts: list[dict[str, object]] = []
    try:
        for ordinal, record in enumerate(records, start=1):
            print(
                f"E058-KERNEL-CORE-START ordinal={ordinal}/{len(records)} label={record['label']}",
                flush=True,
            )
            receipts.append(
                compile_core(
                    core_directory=core_directory,
                    record=record,
                    work_directory=work_directory,
                    source_directory=source_directory,
                    timeout_seconds=args.timeout_seconds,
                )
            )
            partial = {
                "schema_version": 1,
                "complete": False,
                "requested_cores": len(records),
                "passed_cores": len(receipts),
                "core_receipt_sha256": sha256_path(aggregate_source),
                "records": receipts,
            }
            write_json(work_directory / "kernel-aggregate-progress.json", partial)
    except (KeyError, OSError, ValueError, subprocess.SubprocessError, KernelImportError) as error:
        raise SystemExit(f"E058-KERNEL-IMPORT-FAILED: {error}") from error
    result = {
        "schema_version": 1,
        "experiment": "E058-R5-SPECIAL-BROOKS-KERNEL-BRIDGE",
        "verification": "LEAN-KERNEL-RUP-UNSAT",
        "audit_runner_sha256": sha256_path(Path(__file__).resolve()),
        "tool_sha256": {
            "audit_runner": sha256_path(Path(__file__).resolve()),
            "module_generator": sha256_path(
                REPOSITORY / "repro/generate_e058_lean_stage_modules.py"
            ),
            "stage_splitter": sha256_path(
                REPOSITORY / "src/split_rup_lrat_stages.py"
            ),
        },
        "complete": True,
        "requested_cores": len(records),
        "passed_cores": len(receipts),
        "core_receipt_sha256": sha256_path(aggregate_source),
        "allowed_axioms": ["propext"],
        "records": receipts,
    }
    result_path = work_directory / "kernel-aggregate-receipt.json"
    write_json(result_path, result)
    print(
        f"E058-KERNEL-IMPORT-PASS cores={len(receipts)} "
        f"receipt_sha256={sha256_path(result_path)}",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

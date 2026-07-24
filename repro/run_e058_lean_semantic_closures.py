#!/usr/bin/env python3
"""Kernel-check exact E058 SAT-to-graph semantic closures.

Each closure starts from a previously imported staged LRAT theorem, reifies
its exact retained CNF propositions, specializes the primary variables to
edges of a graph on 26 vertices, checks the named-clause correspondence by
definitional equality, and eliminates every retained clause from explicit
graph assumptions.  Full branch units are supplied by the independently
hashed E058 unit manifest because backward proof-core minimization can delete
input units that are not needed for propositional unsatisfiability.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
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
PRIMARY_VARIABLES = 26 * 25 // 2
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
RESOURCE_PATTERN = re.compile(
    r"E058_SEMANTIC_RESOURCE wall=(?P<wall>[0-9.]+) "
    r"max_rss_kb=(?P<rss>[0-9]+) exit=(?P<exit>[0-9]+)"
)


class SemanticClosureError(RuntimeError):
    """Raised when an exact semantic-closure audit gate fails."""


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def camel_label(label: str) -> str:
    parts = label.split("_")
    if not parts or any(not part.isalnum() for part in parts):
        raise SemanticClosureError(f"unsupported core label: {label}")
    return "".join(part[:1].upper() + part[1:] for part in parts)


def kernel_prefix(label: str) -> str:
    return "E058Kernel" + camel_label(label)


def semantic_prefix(label: str) -> str:
    return "E058Semantic" + camel_label(label)


def read_dimacs_header(path: Path) -> tuple[int, int]:
    header: tuple[int, int] | None = None
    with path.open("r", encoding="ascii") as stream:
        for raw_line in stream:
            line = raw_line.strip()
            if not line or line.startswith("c"):
                continue
            if not line.startswith("p "):
                if header is None:
                    raise SemanticClosureError(f"{path}: clause before DIMACS header")
                break
            fields = line.split()
            if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                raise SemanticClosureError(f"{path}: malformed DIMACS header")
            if header is not None:
                raise SemanticClosureError(f"{path}: duplicate DIMACS header")
            header = (int(fields[2]), int(fields[3]))
    if header is None:
        raise SemanticClosureError(f"{path}: missing DIMACS header")
    return header


def validate_unit_cnf(path: Path) -> tuple[int, list[int]]:
    variable_count, expected_clauses = read_dimacs_header(path)
    units: list[int] = []
    seen: set[int] = set()
    header_seen = False
    with path.open("r", encoding="ascii") as stream:
        for raw_line in stream:
            line = raw_line.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p "):
                if header_seen:
                    raise SemanticClosureError(f"{path}: duplicate DIMACS header")
                header_seen = True
                continue
            if not header_seen:
                raise SemanticClosureError(f"{path}: clause before DIMACS header")
            fields = line.split()
            if len(fields) != 2 or fields[1] != "0":
                raise SemanticClosureError(f"{path}: non-unit support clause")
            literal = int(fields[0])
            if literal == 0 or abs(literal) > PRIMARY_VARIABLES:
                raise SemanticClosureError(f"{path}: invalid primary unit {literal}")
            if literal in seen:
                raise SemanticClosureError(f"{path}: duplicate primary unit {literal}")
            if -literal in seen:
                raise SemanticClosureError(
                    f"{path}: contradictory primary unit {literal}"
                )
            seen.add(literal)
            units.append(literal)
    if len(units) != expected_clauses:
        raise SemanticClosureError(
            f"{path}: parsed {len(units)} units, expected {expected_clauses}"
        )
    return variable_count, units


def comparison_scheme(variable_count: int) -> str:
    if variable_count == 3930:
        return "full_exterior"
    if variable_count == 3920:
        return "zero_anchor"
    raise SemanticClosureError(
        f"unsupported E058 variable allocation size: {variable_count}"
    )


def lean_string(path: Path) -> str:
    return json.dumps(os.path.relpath(path.resolve(), LEAN_ROOT.resolve()))


def render_semantic_source(
    *,
    label: str,
    final_kernel_module: str,
    final_kernel_theorem: str,
    kernel_context: str,
    variable_count: int,
    scheme: str,
    core_path: Path,
    unit_path: Path,
) -> tuple[str, str, str]:
    prefix = semantic_prefix(label)
    module_name = prefix + "Closure"
    theorem_name = prefix + "Contradiction"
    reified = prefix + "Reified"
    graph_formula = prefix + "GraphFormula"
    named_core = prefix + "NamedCore"
    body = (
        "import Erdos617.Sat.R5CoreSemantics\n"
        f"import {final_kernel_module}\n\n"
        "set_option maxHeartbeats 0 in\n"
        f"lrat_reify_stored {reified} {variable_count}\n"
        f"  {kernel_context}\n"
        f"  {final_kernel_theorem}\n\n"
        "set_option maxHeartbeats 0 in\n"
        f"r5_specialize_reified {graph_formula}\n"
        f"  {scheme} {reified}\n\n"
        "set_option maxHeartbeats 0 in\n"
        f"r5_map_reified_core {named_core}\n"
        f"  {scheme} {graph_formula}\n"
        f"  {lean_string(core_path)}\n\n"
        "set_option maxHeartbeats 0 in\n"
        "r5_close_reified_core_with_units\n"
        f"  {theorem_name}\n"
        f"  {scheme} {named_core}\n"
        f"  {lean_string(core_path)}\n"
        f"  {lean_string(unit_path)}\n\n"
        f"#print axioms {theorem_name}\n"
        f"#check {theorem_name}\n"
    )
    return module_name, theorem_name, body


def fresh_audit_source(module_name: str, theorem_name: str) -> str:
    return (
        f"import {module_name}\n\n"
        f"#print axioms {theorem_name}\n"
        f"#check {theorem_name}\n"
    )


def validate_axioms(output: str, theorem_name: str) -> str:
    expected = (
        f"'{theorem_name}' depends on axioms: "
        "[propext, Classical.choice, Quot.sound]"
    )
    lines = [line.strip() for line in output.splitlines() if "depends on axioms:" in line]
    if lines != [expected]:
        raise SemanticClosureError(
            f"axiom audit mismatch for {theorem_name}: {lines}"
        )
    return expected


def validate_theorem_output(output: str, theorem_name: str) -> None:
    if theorem_name not in output:
        raise SemanticClosureError(f"missing #check output for {theorem_name}")
    if "R5CoreAssumptions" not in output or "False" not in output:
        raise SemanticClosureError(
            f"conditional contradiction type audit failed for {theorem_name}"
        )


def run_lean(
    *,
    source: Path,
    output: Path | None,
    timeout_seconds: int,
    memory_megabytes: int,
    log_path: Path,
) -> dict[str, object]:
    command = [
        "/usr/bin/time",
        "-f",
        "E058_SEMANTIC_RESOURCE wall=%e max_rss_kb=%M exit=%x",
        str(LEAN_BIN),
        "env",
        "lean",
        "-j1",
        f"-M{memory_megabytes}",
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
        raise SemanticClosureError(f"Lean timeout for {source.name}") from error
    combined = result.stdout + result.stderr
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(combined, encoding="utf-8", newline="\n")
    if result.returncode != 0:
        raise SemanticClosureError(
            f"Lean failed for {source.name} with {result.returncode}; see {log_path}"
        )
    matches = list(RESOURCE_PATTERN.finditer(combined))
    if len(matches) != 1 or int(matches[0].group("exit")) != 0:
        raise SemanticClosureError(f"missing successful resource record for {source.name}")
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


def locate_kernel_receipt(label: str, roots: list[Path]) -> Path:
    candidates = {
        (root / label / "kernel-receipt.json").resolve()
        for root in roots
        if (root / label / "kernel-receipt.json").is_file()
    }
    if not candidates:
        raise SemanticClosureError(f"no completed kernel receipt for {label}")
    if len(candidates) != 1:
        raise SemanticClosureError(
            f"ambiguous completed kernel receipts for {label}: "
            f"{sorted(map(str, candidates))}"
        )
    return candidates.pop()


def verify_inputs(
    *,
    core_directory: Path,
    record: dict[str, object],
    unit_record: dict[str, object],
    kernel_receipt_roots: list[Path],
) -> dict[str, object]:
    label = str(record["label"])
    if unit_record.get("label") != label:
        raise SemanticClosureError(f"unit manifest label mismatch for {label}")
    core = record["core"]
    core_path = core_directory / str(core["cnf_path"])
    if not core_path.is_file() or sha256_path(core_path) != core["cnf_sha256"]:
        raise SemanticClosureError(f"reduced core CNF hash mismatch for {label}")
    core_variables, core_clauses = read_dimacs_header(core_path)
    if core_clauses != core["original_clauses"]:
        raise SemanticClosureError(f"reduced core clause-count mismatch for {label}")

    unit_path = REPOSITORY / str(unit_record["unit_cnf"])
    if not unit_path.is_file() or sha256_path(unit_path) != unit_record["unit_cnf_sha256"]:
        raise SemanticClosureError(f"unit CNF hash mismatch for {label}")
    unit_variables, units = validate_unit_cnf(unit_path)
    if unit_variables != core_variables:
        raise SemanticClosureError(f"core/unit variable-count mismatch for {label}")
    if len(units) != unit_record["unit_count"]:
        raise SemanticClosureError(f"unit manifest count mismatch for {label}")
    if sum(literal > 0 for literal in units) != unit_record["positive_units"]:
        raise SemanticClosureError(f"positive-unit count mismatch for {label}")
    if sum(literal < 0 for literal in units) != unit_record["negative_units"]:
        raise SemanticClosureError(f"negative-unit count mismatch for {label}")
    if core_variables != unit_record["source_variables"]:
        raise SemanticClosureError(f"source allocation mismatch for {label}")

    kernel_receipt_path = locate_kernel_receipt(label, kernel_receipt_roots)
    kernel_receipt = json.loads(kernel_receipt_path.read_text(encoding="ascii"))
    if kernel_receipt.get("verification") != "LEAN-KERNEL-RUP-UNSAT":
        raise SemanticClosureError(f"kernel verification level mismatch for {label}")
    if kernel_receipt.get("label") != label:
        raise SemanticClosureError(f"kernel receipt label mismatch for {label}")
    if kernel_receipt["core"]["cnf_sha256"] != core["cnf_sha256"]:
        raise SemanticClosureError(f"kernel/core CNF mismatch for {label}")
    expected_kernel_theorem = kernel_prefix(label) + "KernelProof"
    if kernel_receipt["final_theorem"] != expected_kernel_theorem:
        raise SemanticClosureError(f"kernel theorem mismatch for {label}")
    compiled_stages = kernel_receipt.get("compiled_stages")
    if not isinstance(compiled_stages, list) or not compiled_stages:
        raise SemanticClosureError(f"kernel receipt has no stages for {label}")
    final_kernel_module = str(compiled_stages[-1]["module"])
    kernel_context = (
        expected_kernel_theorem + ".ctx"
        if len(compiled_stages) == 1
        else str(compiled_stages[0]["module"]) + ".ctx"
    )
    final_olean = Path(str(kernel_receipt["final_olean"]["path"]))
    if (
        not final_olean.is_file()
        or sha256_path(final_olean) != kernel_receipt["final_olean"]["sha256"]
    ):
        raise SemanticClosureError(f"kernel olean hash mismatch for {label}")
    expected_kernel_axiom = (
        f"'{expected_kernel_theorem}' depends on axioms: [propext]"
    )
    if kernel_receipt["fresh_audit"]["axiom_audit"] != expected_kernel_axiom:
        raise SemanticClosureError(f"kernel axiom audit mismatch for {label}")

    return {
        "label": label,
        "core_path": core_path,
        "core_variables": core_variables,
        "core_clauses": core_clauses,
        "unit_path": unit_path,
        "unit_count": len(units),
        "scheme": comparison_scheme(core_variables),
        "kernel_receipt_path": kernel_receipt_path,
        "kernel_receipt": kernel_receipt,
        "final_kernel_module": final_kernel_module,
        "final_kernel_theorem": expected_kernel_theorem,
        "kernel_context": kernel_context,
        "final_kernel_olean": final_olean,
    }


def completed_receipt_is_current(
    receipt: dict[str, object],
    *,
    verified: dict[str, object],
    module_name: str,
    theorem_name: str,
    source_path: Path,
    output_path: Path,
    core_path: Path,
    unit_path: Path,
    kernel_receipt_path: Path,
) -> bool:
    expected_axiom = (
        f"'{theorem_name}' depends on axioms: "
        "[propext, Classical.choice, Quot.sound]"
    )
    sections = {
        name: receipt.get(name)
        for name in ("core", "units", "kernel_import", "olean", "compile", "fresh_audit")
    }
    if any(not isinstance(section, dict) for section in sections.values()):
        return False
    core_record = sections["core"]
    unit_record = sections["units"]
    kernel_record = sections["kernel_import"]
    olean_record = sections["olean"]
    compile_record = sections["compile"]
    audit_record = sections["fresh_audit"]
    if (
        not isinstance(compile_record.get("log"), dict)
        or not isinstance(audit_record.get("log"), dict)
        or not output_path.is_file()
    ):
        return False
    audit_path = source_path.parent / f"{module_name}FreshAudit.lean"
    compile_log = Path(str(compile_record["log"].get("path", "")))
    audit_log = Path(str(audit_record["log"].get("path", "")))
    kernel_receipt = verified["kernel_receipt"]
    if (
        receipt.get("verification") != "LEAN-KERNEL-CONDITIONAL-GRAPH-UNSAT"
        or receipt.get("label") != verified["label"]
        or receipt.get("comparison_scheme") != verified["scheme"]
        or receipt.get("theorem") != theorem_name
        or receipt.get("source") != str(source_path)
        or core_record.get("variables") != verified["core_variables"]
        or core_record.get("clauses") != verified["core_clauses"]
        or core_record.get("path") != str(core_path)
        or unit_record.get("count") != verified["unit_count"]
        or unit_record.get("path") != str(unit_path)
        or kernel_record.get("receipt") != str(kernel_receipt_path)
        or kernel_record.get("theorem") != verified["final_kernel_theorem"]
        or kernel_record.get("module") != verified["final_kernel_module"]
        or kernel_record.get("context") != verified["kernel_context"]
        or kernel_record.get("olean_sha256")
        != kernel_receipt["final_olean"]["sha256"]
        or olean_record.get("path") != str(output_path)
        or olean_record.get("bytes") != output_path.stat().st_size
        or compile_record.get("axiom_audit") != expected_axiom
        or audit_record.get("axiom_audit") != expected_axiom
        or not audit_path.is_file()
        or audit_path.read_text(encoding="ascii")
        != fresh_audit_source(module_name, theorem_name)
    ):
        return False
    expected = (
        (source_path, receipt.get("source_sha256")),
        (output_path, olean_record.get("sha256")),
        (core_path, core_record.get("sha256")),
        (unit_path, unit_record.get("sha256")),
        (
            kernel_receipt_path,
            kernel_record.get("receipt_sha256"),
        ),
        (compile_log, compile_record["log"].get("sha256")),
        (audit_log, audit_record["log"].get("sha256")),
    )
    if not all(
        path.is_file() and isinstance(digest, str) and sha256_path(path) == digest
        for path, digest in expected
    ):
        return False
    for run, log in (
        (compile_record, compile_log),
        (audit_record, audit_log),
    ):
        if (
            run.get("log", {}).get("bytes") != log.stat().st_size
            or "warning:" in log.read_text(encoding="utf-8").lower()
        ):
            return False
    return True


def compile_closure(
    *,
    verified: dict[str, object],
    source_directory: Path,
    work_directory: Path,
    timeout_seconds: int,
    memory_megabytes: int,
) -> dict[str, object]:
    label = str(verified["label"])
    core_path = Path(verified["core_path"])
    unit_path = Path(verified["unit_path"])
    kernel_receipt_path = Path(verified["kernel_receipt_path"])
    source_root = source_directory / label
    work_root = work_directory / label
    logs_root = work_root / "logs"
    source_root.mkdir(parents=True, exist_ok=True)
    work_root.mkdir(parents=True, exist_ok=True)

    module_name, theorem_name, source_text = render_semantic_source(
        label=label,
        final_kernel_module=str(verified["final_kernel_module"]),
        final_kernel_theorem=str(verified["final_kernel_theorem"]),
        kernel_context=str(verified["kernel_context"]),
        variable_count=int(verified["core_variables"]),
        scheme=str(verified["scheme"]),
        core_path=core_path,
        unit_path=unit_path,
    )
    source_path = source_root / f"{module_name}.lean"
    if source_path.is_file():
        if source_path.read_text(encoding="ascii") != source_text:
            if (work_root / "semantic-receipt.json").is_file():
                raise SemanticClosureError(f"stale semantic source for {label}")
            source_path.write_text(source_text, encoding="ascii", newline="\n")
    else:
        source_path.write_text(source_text, encoding="ascii", newline="\n")
    output_path = LEAN_ROOT / ".lake/build/lib/lean" / f"{module_name}.olean"
    receipt_path = work_root / "semantic-receipt.json"
    if receipt_path.is_file():
        receipt = json.loads(receipt_path.read_text(encoding="ascii"))
        if completed_receipt_is_current(
            receipt,
            verified=verified,
            module_name=module_name,
            theorem_name=theorem_name,
            source_path=source_path,
            output_path=output_path,
            core_path=core_path,
            unit_path=unit_path,
            kernel_receipt_path=kernel_receipt_path,
        ):
            print(
                f"E058-SEMANTIC-CORE-SKIP label={label} reason=verified-receipt",
                flush=True,
            )
            return receipt
        raise SemanticClosureError(f"stale completed semantic receipt for {label}")

    print(f"E058-SEMANTIC-COMPILE-START label={label}", flush=True)
    compile_run = run_lean(
        source=source_path,
        output=output_path,
        timeout_seconds=timeout_seconds,
        memory_megabytes=memory_megabytes,
        log_path=logs_root / "compile.log",
    )
    compile_output = str(compile_run.pop("output"))
    compile_axiom = validate_axioms(compile_output, theorem_name)
    validate_theorem_output(compile_output, theorem_name)

    audit_path = source_root / f"{module_name}FreshAudit.lean"
    audit_text = fresh_audit_source(module_name, theorem_name)
    if audit_path.is_file():
        if audit_path.read_text(encoding="ascii") != audit_text:
            raise SemanticClosureError(f"stale semantic fresh-audit source for {label}")
    else:
        audit_path.write_text(audit_text, encoding="ascii", newline="\n")
    audit_run = run_lean(
        source=audit_path,
        output=None,
        timeout_seconds=timeout_seconds,
        memory_megabytes=memory_megabytes,
        log_path=logs_root / "fresh-audit.log",
    )
    audit_output = str(audit_run.pop("output"))
    audit_axiom = validate_axioms(audit_output, theorem_name)
    validate_theorem_output(audit_output, theorem_name)

    kernel_receipt = verified["kernel_receipt"]
    receipt: dict[str, object] = {
        "schema_version": 1,
        "experiment": "E058-R5-SPECIAL-BROOKS-KERNEL-BRIDGE",
        "label": label,
        "verification": "LEAN-KERNEL-CONDITIONAL-GRAPH-UNSAT",
        "scope": (
            "Exact retained CNF contradiction under R5CoreAssumptions and "
            "the pinned branch-unit assignment"
        ),
        "comparison_scheme": verified["scheme"],
        "theorem": theorem_name,
        "source": str(source_path),
        "source_sha256": sha256_path(source_path),
        "core": {
            "path": str(core_path),
            "variables": verified["core_variables"],
            "clauses": verified["core_clauses"],
            "sha256": sha256_path(core_path),
        },
        "units": {
            "path": str(unit_path),
            "count": verified["unit_count"],
            "sha256": sha256_path(unit_path),
        },
        "kernel_import": {
            "receipt": str(kernel_receipt_path),
            "receipt_sha256": sha256_path(kernel_receipt_path),
            "theorem": verified["final_kernel_theorem"],
            "module": verified["final_kernel_module"],
            "context": verified["kernel_context"],
            "olean_sha256": kernel_receipt["final_olean"]["sha256"],
        },
        "olean": {
            "path": str(output_path),
            "bytes": output_path.stat().st_size,
            "sha256": sha256_path(output_path),
        },
        "compile": {"axiom_audit": compile_axiom, **compile_run},
        "fresh_audit": {"axiom_audit": audit_axiom, **audit_run},
    }
    write_json(receipt_path, receipt)
    print(
        "E058-SEMANTIC-CORE-PASS "
        f"label={label} scheme={verified['scheme']} "
        f"clauses={verified['core_clauses']} units={verified['unit_count']} "
        f"theorem={theorem_name}",
        flush=True,
    )
    return receipt


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--core-directory", type=Path, required=True)
    parser.add_argument("--unit-manifest", type=Path, required=True)
    parser.add_argument(
        "--kernel-receipt-root", type=Path, action="append", required=True
    )
    parser.add_argument("--source-directory", type=Path, required=True)
    parser.add_argument("--work-directory", type=Path, required=True)
    parser.add_argument("--only", action="append", default=[])
    parser.add_argument("--timeout-seconds", type=int, default=1200)
    parser.add_argument("--memory-megabytes", type=int, default=12288)
    args = parser.parse_args()

    core_directory = args.core_directory.resolve()
    unit_manifest_path = args.unit_manifest.resolve()
    kernel_receipt_roots = [path.resolve() for path in args.kernel_receipt_root]
    source_directory = args.source_directory.resolve()
    work_directory = args.work_directory.resolve()
    try:
        source_directory.relative_to(LEAN_ROOT.resolve())
    except ValueError as error:
        raise SystemExit("source directory must be inside the Lean package root") from error

    try:
        aggregate_path = core_directory / "receipt.json"
        aggregate = json.loads(aggregate_path.read_text(encoding="ascii"))
        unit_manifest = json.loads(unit_manifest_path.read_text(encoding="ascii"))
        unit_records = {
            str(record["label"]): record for record in unit_manifest["records"]
        }
        records = aggregate["records"]
        selected = set(args.only)
        if selected:
            known = {str(record["label"]) for record in records}
            unknown = selected - known
            if unknown:
                raise SemanticClosureError(
                    f"unknown --only labels: {sorted(unknown)}"
                )
            records = [
                record for record in records if str(record["label"]) in selected
            ]
        missing_units = [
            str(record["label"])
            for record in records
            if str(record["label"]) not in unit_records
        ]
        if missing_units:
            raise SemanticClosureError(
                f"unit manifest missing labels: {missing_units}"
            )
        source_directory.mkdir(parents=True, exist_ok=True)
        work_directory.mkdir(parents=True, exist_ok=True)
        receipts: list[dict[str, object]] = []
        for ordinal, record in enumerate(records, start=1):
            label = str(record["label"])
            print(
                f"E058-SEMANTIC-CORE-START ordinal={ordinal}/{len(records)} "
                f"label={label}",
                flush=True,
            )
            verified = verify_inputs(
                core_directory=core_directory,
                record=record,
                unit_record=unit_records[label],
                kernel_receipt_roots=kernel_receipt_roots,
            )
            receipts.append(
                compile_closure(
                    verified=verified,
                    source_directory=source_directory,
                    work_directory=work_directory,
                    timeout_seconds=args.timeout_seconds,
                    memory_megabytes=args.memory_megabytes,
                )
            )
            write_json(
                work_directory / "semantic-aggregate-progress.json",
                {
                    "schema_version": 1,
                    "complete": False,
                    "requested_cores": len(records),
                    "passed_cores": len(receipts),
                    "core_receipt_sha256": sha256_path(aggregate_path),
                    "unit_manifest_sha256": sha256_path(unit_manifest_path),
                    "records": receipts,
                },
            )
    except (
        KeyError,
        OSError,
        TypeError,
        ValueError,
        json.JSONDecodeError,
        subprocess.SubprocessError,
        SemanticClosureError,
    ) as error:
        raise SystemExit(f"E058-SEMANTIC-CLOSURE-FAILED: {error}") from error

    result = {
        "schema_version": 1,
        "experiment": "E058-R5-SPECIAL-BROOKS-KERNEL-BRIDGE",
        "verification": "LEAN-KERNEL-CONDITIONAL-GRAPH-UNSAT",
        "audit_runner_sha256": sha256_path(Path(__file__).resolve()),
        "tool_sha256": {
            "audit_runner": sha256_path(Path(__file__).resolve()),
        },
        "scope": (
            "Exact retained CNF contradictions under per-core "
            "R5CoreAssumptions and pinned branch-unit assignments"
        ),
        "complete": True,
        "requested_cores": len(records),
        "passed_cores": len(receipts),
        "core_receipt_sha256": sha256_path(aggregate_path),
        "unit_manifest_sha256": sha256_path(unit_manifest_path),
        "allowed_axioms": ALLOWED_AXIOMS,
        "records": receipts,
    }
    result_path = work_directory / "semantic-aggregate-receipt.json"
    write_json(result_path, result)
    print(
        f"E058-SEMANTIC-CLOSURE-PASS cores={len(receipts)} "
        f"receipt_sha256={sha256_path(result_path)}",
        flush=True,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

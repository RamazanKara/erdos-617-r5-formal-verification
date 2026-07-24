#!/usr/bin/env python3
"""Run the complete fresh E058 proof-core, Lean, and axiom audit.

The input repository may reuse a read-only package cache and the committed
compressed CNF/LRAT containers.  It must not contain a local Lean build when
``--require-no-local-build`` is supplied.  Every E058 reduced core, staged
kernel theorem, graph-semantic closure, coverage module, and final fixed-r=5
theorem is then rebuilt in that repository.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

LEAN_TOOLCHAIN = "leanprover/lean4:v4.32.0"
LEAN_COMMIT = "8c9756b28d64dab099da31a4c09229a9e6a2ef35"
MATHLIB_REVISION = "81a5d257c8e410db227a6665ed08f64fea08e997"
LAKE_MANIFEST_SHA256 = (
    "acfc19d483c350eb6dad0e0d02681ccc167db7e44446e3c3f4ef74067d2b4267"
)
EXPECTED_LABELS = 89
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
LEGACY_CLEAN_START_RUNNER_SHA256 = (
    "c69d27f7ca1cc5c98c087c287f832ca9d1ed4925d21f4166f762af1c0b37fb72"
)
CLEAN_START_MARKERS = (
    "E058-CERTIFICATE-REGENERATION-PASS certificates=3",
    "Build completed successfully (1315 jobs).",
    (
        "E058-RUP-CORES-PASS cores=89 c_checks=89 "
        "python_checks=89 negative_checks=356 zero_rat=89"
    ),
)
FORBIDDEN_SOURCE = re.compile(
    r"\bsorry\b|\badmit\b|^[ \t]*axiom\b|^[ \t]*unsafe\b|"
    r"native_decide|ofReduceBool|run_tac",
    flags=re.MULTILINE,
)

COVERAGE_MODULES = (
    "E058E038Coverage",
    "E058E042DirectCoverage",
    "E058E043P04Coverage",
    "E058E043P09Coverage",
    "E058E043P19Coverage",
    "E058E042Coverage",
    "E058E045Coverage",
    "E058SpecialBrooksCoverage",
)

COVERAGE_THEOREMS = (
    "Erdos617.e058E038Contradiction",
    "Erdos617.e058E042DirectContradiction",
    "Erdos617.e058E043P04Contradiction",
    "Erdos617.e058E043P09Contradiction",
    "Erdos617.e058E043P19Contradiction",
    "Erdos617.e058E042CanonicalContradiction",
    "Erdos617.e058E045Contradiction",
    "Erdos617.e058E045CanonicalContradiction",
    "Erdos617.e058SpecialBrooksBranchContradiction",
    "Erdos617.e058SpecialBrooksContradiction",
    "Erdos617.e058R5SpecialBrooksObstruction",
    "Erdos617.e058NoR5Counterexample",
    "Erdos617.e058R5Upper",
    "Erdos617.e058Problem617AtFive",
)

LEAN_LIBRARY_TARGETS = (
    "Erdos617.Sat.LRATStage",
    "Erdos617.Sat.R5CoreSemantics",
    "Erdos617.Sat.NeighborhoodOrbitCertificate",
    "Erdos617.Sat.NeighborhoodCrossPatternCertificate",
    "Erdos617.Sat.ZeroAnchorOrbitCertificate",
    "Erdos617.Sat.SpecialBrooksE043P04Bridge",
    "Erdos617.Sat.SpecialBrooksE043P09Bridge",
    "Erdos617.Sat.SpecialBrooksE043P19Bridge",
    "Erdos617.Sat.SpecialBrooksE045Bridge",
)


class AuditError(RuntimeError):
    """Raised when a mandatory E058 audit gate fails."""


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def camel_label(label: str) -> str:
    parts = label.split("_")
    if not parts or any(not part.isalnum() for part in parts):
        raise AuditError(f"unsupported E058 label: {label}")
    return "".join(part[:1].upper() + part[1:] for part in parts)


def locate_roots(project: Path) -> tuple[Path, Path]:
    project = project.resolve()
    if (project / "formal/lean/lakefile.toml").is_file():
        return project, project / "formal/lean"
    if (project / "lakefile.toml").is_file() and project.name == "lean":
        repository = project.parents[1]
        if (repository / "repro").is_dir():
            return repository, project
    raise AuditError(
        "--project must be a repository root containing formal/lean or "
        "the formal/lean package root"
    )


def source_inventory(lean_root: Path) -> list[Path]:
    roots = [
        lean_root / "Erdos617.lean",
        *sorted((lean_root / "Erdos617").rglob("*.lean")),
        *(lean_root / f"{module}.lean" for module in COVERAGE_MODULES),
    ]
    unique = sorted(set(roots))
    if not unique or any(not path.is_file() for path in unique):
        missing = [str(path) for path in unique if not path.is_file()]
        raise AuditError(f"audited Lean source inventory is incomplete: {missing}")
    return unique


def inventory_hashes(paths: list[Path], root: Path) -> dict[str, str]:
    return {
        str(path.relative_to(root)): sha256_path(path)
        for path in sorted(paths)
    }


def combined_inventory_sha256(inventory: dict[str, str]) -> str:
    digest = hashlib.sha256()
    for path, value in sorted(inventory.items()):
        digest.update(path.encode("utf-8"))
        digest.update(b"\0")
        digest.update(value.encode("ascii"))
        digest.update(b"\n")
    return digest.hexdigest()


class Transcript:
    def __init__(self, path: Path, *, append: bool = False) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        self.path = path
        self.stream = path.open(
            "a" if append else "w", encoding="utf-8", newline="\n"
        )

    def close(self) -> None:
        self.stream.close()

    def note(self, message: str) -> None:
        line = message.rstrip("\n") + "\n"
        self.stream.write(line)
        self.stream.flush()
        print(line, end="", flush=True)

    def run(
        self,
        command: list[str],
        *,
        cwd: Path,
        environment: dict[str, str],
        lean_gate: bool = False,
    ) -> tuple[str, float]:
        self.note("$ " + " ".join(command))
        started = time.monotonic()
        process = subprocess.Popen(
            command,
            cwd=cwd,
            env=environment,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )
        assert process.stdout is not None
        chunks: list[str] = []
        for line in process.stdout:
            chunks.append(line)
            self.stream.write(line)
            self.stream.flush()
            print(line, end="", flush=True)
        return_code = process.wait()
        elapsed = time.monotonic() - started
        output = "".join(chunks)
        if return_code != 0:
            raise AuditError(
                f"command returned {return_code}: {' '.join(command)}"
            )
        if lean_gate and "warning:" in output.lower():
            raise AuditError(f"Lean command emitted a warning: {' '.join(command)}")
        return output, elapsed


def validate_pins(lean_root: Path, lake: Path, transcript: Transcript) -> None:
    if not lake.is_file():
        raise AuditError(f"Lean Lake executable is missing: {lake}")
    toolchain = (lean_root / "lean-toolchain").read_text(encoding="ascii").strip()
    if toolchain != LEAN_TOOLCHAIN:
        raise AuditError(f"Lean toolchain pin differs: {toolchain}")
    manifest_path = lean_root / "lake-manifest.json"
    if sha256_path(manifest_path) != LAKE_MANIFEST_SHA256:
        raise AuditError("complete Lake package manifest hash differs")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    mathlib = next(
        package for package in manifest["packages"] if package["name"] == "mathlib"
    )
    if mathlib["rev"] != MATHLIB_REVISION:
        raise AuditError(f"mathlib revision pin differs: {mathlib['rev']}")
    transcript.note(
        "E058-PINS-PASS "
        f"lean_toolchain={LEAN_TOOLCHAIN} mathlib={MATHLIB_REVISION} "
        f"lake_manifest_sha256={LAKE_MANIFEST_SHA256}"
    )


def validate_forbidden_sources(paths: list[Path], root: Path) -> None:
    hits = [
        str(path.relative_to(root))
        for path in paths
        if FORBIDDEN_SOURCE.search(path.read_text(encoding="utf-8"))
    ]
    if hits:
        raise AuditError(f"forbidden source construct in: {hits}")


def regenerate_certificates(
    *,
    repository: Path,
    lean_root: Path,
    work: Path,
    transcript: Transcript,
    environment: dict[str, str],
) -> dict[str, str]:
    regenerated = work / "regenerated-certificates"
    regenerated.mkdir(parents=True, exist_ok=True)
    jobs = (
        (
            repository / "repro/generate_e058_neighborhood_orbit_certificate.py",
            lean_root / "Erdos617/Sat/NeighborhoodOrbitCertificate.lean",
        ),
        (
            repository / "repro/generate_e058_cross_pattern_certificate.py",
            lean_root / "Erdos617/Sat/NeighborhoodCrossPatternCertificate.lean",
        ),
        (
            repository / "repro/generate_e058_zero_anchor_orbit_certificate.py",
            lean_root / "Erdos617/Sat/ZeroAnchorOrbitCertificate.lean",
        ),
    )
    result: dict[str, str] = {}
    for script, expected in jobs:
        output = regenerated / expected.name
        transcript.run(
            [sys.executable, str(script), str(output)],
            cwd=repository,
            environment=environment,
        )
        if output.read_bytes() != expected.read_bytes():
            raise AuditError(
                f"generated certificate differs from committed source: {expected}"
            )
        result[str(expected.relative_to(repository))] = sha256_path(expected)
    transcript.note(
        "E058-CERTIFICATE-REGENERATION-PASS "
        f"certificates={len(result)}"
    )
    return result


def validate_core_receipt(
    path: Path, repository: Path
) -> dict[str, object]:
    receipt = json.loads(path.read_text(encoding="ascii"))
    records = receipt.get("records")
    if (
        receipt.get("inventory_count") != EXPECTED_LABELS
        or receipt.get("full_inventory") is not True
        or receipt.get("rup_only") is not True
        or receipt.get("negative_checks") != 4 * EXPECTED_LABELS
        or not isinstance(records, list)
        or len(records) != EXPECTED_LABELS
    ):
        raise AuditError("E058 reduced-core receipt has the wrong scope")
    labels = [str(record["label"]) for record in records]
    if len(set(labels)) != EXPECTED_LABELS:
        raise AuditError("E058 reduced-core labels are not unique")
    expected_tools = {
        "minimizer": sha256_path(repository / "src/minimize_rup_lrat.py"),
        "c_lrat_checker": sha256_path(
            repository / "build/lrat-check-upstream"
        ),
        "python_lrat_checker": sha256_path(
            repository / "src/check_lrat.py"
        ),
    }
    if receipt.get("tool_sha256") != expected_tools:
        raise AuditError("E058 reduced-core tool hashes differ")
    for record in records:
        if "VERIFIED" not in str(record.get("c_checker_output", "")):
            raise AuditError(f"C checker output is not verified: {record['label']}")
        if "LRAT-VALID" not in str(record.get("python_checker_output", "")):
            raise AuditError(
                f"Python checker output is not verified: {record['label']}"
            )
        source = record["source"]
        for path_key, hash_key in (
            ("cnf_path", "cnf_container_sha256"),
            ("proof_path", "proof_container_sha256"),
        ):
            artifact = repository / str(source[path_key])
            if (
                not artifact.is_file()
                or sha256_path(artifact) != source[hash_key]
            ):
                raise AuditError(
                    f"E058 source container mismatch: "
                    f"{record['label']}.{path_key}"
                )
        core = record["core"]
        if core.get("rat_additions") != 0:
            raise AuditError(f"E058 core contains RAT: {record['label']}")
        for path_key, hash_key in (
            ("cnf_path", "cnf_sha256"),
            ("proof_path", "proof_sha256"),
            ("map_path", "map_sha256"),
        ):
            artifact = path.parent / str(core[path_key])
            if not artifact.is_file() or sha256_path(artifact) != core[hash_key]:
                raise AuditError(
                    f"E058 reduced-core artifact mismatch: "
                    f"{record['label']}.{path_key}"
                )
    return receipt


def validate_unit_manifest(
    generated_path: Path,
    expected_path: Path,
    labels: set[str],
    repository: Path,
) -> dict[str, object]:
    generated = json.loads(generated_path.read_text(encoding="ascii"))
    expected = json.loads(expected_path.read_text(encoding="ascii"))
    generated_records = {
        str(record["label"]): record for record in generated["records"]
    }
    expected_records = {
        str(record["label"]): record for record in expected["records"]
    }
    if set(generated_records) != labels or set(expected_records) != labels:
        raise AuditError("E058 core/unit label inventories differ")
    compared_fields = (
        "source_raw_sha256",
        "source_variables",
        "source_clauses",
        "unit_count",
        "positive_units",
        "negative_units",
        "unit_cnf_bytes",
        "unit_cnf_sha256",
    )
    for label in sorted(labels):
        for field in compared_fields:
            if generated_records[label][field] != expected_records[label][field]:
                raise AuditError(
                    f"E058 unit manifest mismatch for {label}.{field}"
                )
        for origin, record in (
            ("generated", generated_records[label]),
            ("committed", expected_records[label]),
        ):
            unit_path = repository / str(record["unit_cnf"])
            if (
                not unit_path.is_file()
                or unit_path.stat().st_size != record["unit_cnf_bytes"]
                or sha256_path(unit_path) != record["unit_cnf_sha256"]
            ):
                raise AuditError(f"E058 {origin} unit CNF mismatch for {label}")
    return generated


def validate_aggregate(
    path: Path,
    *,
    verification: str,
    labels: set[str],
    tools: dict[str, Path],
) -> dict[str, object]:
    receipt = json.loads(path.read_text(encoding="ascii"))
    records = receipt.get("records")
    expected_tools = {
        name: sha256_path(tool) for name, tool in sorted(tools.items())
    }
    if (
        receipt.get("complete") is not True
        or receipt.get("requested_cores") != EXPECTED_LABELS
        or receipt.get("passed_cores") != EXPECTED_LABELS
        or receipt.get("verification") != verification
        or receipt.get("tool_sha256") != expected_tools
        or not isinstance(records, list)
    ):
        raise AuditError(f"incomplete E058 aggregate receipt: {path}")
    observed = {str(record["label"]) for record in records}
    if observed != labels or len(records) != EXPECTED_LABELS:
        raise AuditError(f"E058 aggregate label mismatch: {path}")
    return receipt


def validate_clean_start_receipt(path: Path) -> dict[str, object]:
    receipt = json.loads(path.read_text(encoding="ascii"))
    if receipt.get("verification") == "CLEAN-START-SEQUENCE-PROVENANCE":
        counts = receipt.get("proof_counts", {})
        source_inventory = receipt.get("source_inventory", {})
        root = path.resolve().parent

        def checked_record(
            record: object,
            *,
            hash_key: str = "sha256",
        ) -> Path:
            if not isinstance(record, dict):
                raise AuditError("clean-start evidence record is malformed")
            candidate = (root / str(record.get("path", ""))).resolve()
            try:
                candidate.relative_to(root)
            except ValueError as error:
                raise AuditError(
                    "clean-start evidence path escapes its receipt directory"
                ) from error
            if (
                not candidate.is_file()
                or candidate.stat().st_size != record.get("bytes")
                or sha256_path(candidate) != record.get(hash_key)
            ):
                raise AuditError(
                    f"clean-start evidence file differs: {candidate}"
                )
            return candidate

        if (
            receipt.get("complete") is not True
            or receipt.get("fresh_local_build") is not True
            or receipt.get("resumed_after_core_replay") is not True
            or counts.get("cores") != EXPECTED_LABELS
            or counts.get("kernel_imports") != EXPECTED_LABELS
            or counts.get("semantic_closures") != EXPECTED_LABELS
            or counts.get("axiom_queries")
            != 2 * EXPECTED_LABELS + len(COVERAGE_THEOREMS)
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
            or not isinstance(receipt.get("audit_runner"), dict)
            or receipt.get("clean_start_markers") != list(CLEAN_START_MARKERS)
            or not isinstance(receipt.get("resume_segments"), int)
            or receipt.get("resume_segments", 0) <= 0
        ):
            raise AuditError(
                "initial E058 clean-start sequence receipt has the wrong scope"
            )
        transcript_path = checked_record(receipt.get("transcript"))
        raw_receipt_path = checked_record(receipt.get("raw_audit_receipt"))
        runner_path = checked_record(
            receipt.get("audit_runner"),
            hash_key="sha256_at_start",
        )
        runner_record = receipt["audit_runner"]
        if runner_record.get("binding") not in {
            "PINNED-LEGACY-RUNNER-SHA256",
            "SELF-HASHED-RUNNER-RECEIPT",
        }:
            raise AuditError("clean-start runner binding is unrecognized")
        if (
            runner_record.get("binding") == "PINNED-LEGACY-RUNNER-SHA256"
            and sha256_path(runner_path) != LEGACY_CLEAN_START_RUNNER_SHA256
        ):
            raise AuditError("pinned legacy clean-start runner hash differs")
        raw_receipt = json.loads(raw_receipt_path.read_text(encoding="ascii"))
        if (
            raw_receipt.get("verification") != "LEAN-KERNEL-FIXED-R5"
            or raw_receipt.get("fresh_local_build") is not True
            or raw_receipt.get("resumed_after_core_replay") is not True
            or raw_receipt.get("cores", {}).get("count") != EXPECTED_LABELS
            or raw_receipt.get("kernel_imports", {}).get("count")
            != EXPECTED_LABELS
            or raw_receipt.get("semantic_closures", {}).get("count")
            != EXPECTED_LABELS
            or raw_receipt.get("axiom_queries", {}).get("count")
            != 2 * EXPECTED_LABELS + len(COVERAGE_THEOREMS)
            or raw_receipt.get("axiom_queries", {}).get("final_theorem")
            != "Erdos617.e058Problem617AtFive"
            or set(
                raw_receipt.get("axiom_queries", {}).get("final_axioms", [])
            )
            != ALLOWED_AXIOMS
            or raw_receipt.get("source_inventory")
            != receipt.get("source_inventory")
            or raw_receipt.get("warnings") != 0
            or raw_receipt.get("forbidden_source_hits") != 0
        ):
            raise AuditError("raw clean-start audit receipt differs in scope")
        if (
            runner_record.get("binding") == "SELF-HASHED-RUNNER-RECEIPT"
            and raw_receipt.get("audit_runner", {}).get("sha256_at_start")
            != sha256_path(runner_path)
        ):
            raise AuditError("self-hashed clean-start runner binding differs")
        transcript = transcript_path.read_text(encoding="utf-8")
        positions = [transcript.find(marker) for marker in CLEAN_START_MARKERS]
        first_resume = transcript.find("E058-FRESH-AUDIT-RESUME ")
        if (
            any(position < 0 for position in positions)
            or positions != sorted(positions)
            or first_resume < 0
            or positions[-1] > first_resume
            or transcript.count("E058-FRESH-AUDIT-RESUME ")
            != receipt["resume_segments"]
        ):
            raise AuditError(
                "clean-start transcript markers are missing or out of order"
            )
        terminal = re.findall(
            (
                r"^E058-FRESH-LEAN-AUDIT-PASS .*"
                r"receipt_sha256=([0-9a-f]{64})$"
            ),
            transcript,
            flags=re.MULTILINE,
        )
        if terminal != [sha256_path(raw_receipt_path)]:
            raise AuditError(
                "clean-start transcript does not bind its raw audit receipt"
            )
        if "warning:" in transcript.lower():
            raise AuditError("clean-start transcript contains a warning")
        return {
            "receipt_sha256": sha256_path(path),
            "verification": receipt["verification"],
            "resumed_after_core_replay": True,
            "source_inventory": receipt["source_inventory"],
            "audit_runner": receipt["audit_runner"],
        }
    raise AuditError(
        "initial E058 clean-start evidence must be a validated "
        "CLEAN-START-SEQUENCE-PROVENANCE receipt"
    )


def scan_logs_for_warnings(root: Path) -> None:
    warned = [
        str(path)
        for path in root.rglob("*.log")
        if "warning:" in path.read_text(encoding="utf-8").lower()
    ]
    if warned:
        raise AuditError(f"Lean stage logs contain warnings: {warned[:10]}")


def render_axiom_audit(labels: list[str]) -> tuple[str, list[str]]:
    kernel = [
        f"E058Kernel{camel_label(label)}KernelProof" for label in labels
    ]
    semantic = [
        f"E058Semantic{camel_label(label)}Contradiction" for label in labels
    ]
    names = [*kernel, *semantic, *COVERAGE_THEOREMS]
    if len(names) != 2 * EXPECTED_LABELS + len(COVERAGE_THEOREMS):
        raise AuditError("E058 axiom-query inventory has the wrong size")
    if len(set(names)) != len(names):
        raise AuditError("E058 axiom-query inventory contains duplicates")
    source = (
        "import E058SpecialBrooksCoverage\n\n"
        + "\n".join(f"#print axioms {name}" for name in names)
        + "\n#check Erdos617.e058Problem617AtFive\n"
    )
    return source, names


def parse_axiom_audit(output: str, names: list[str]) -> dict[str, list[str]]:
    dependencies = re.findall(
        r"'([^']+)' depends on axioms:\s*\[(.*?)\]",
        output,
        flags=re.DOTALL,
    )
    zero = re.findall(
        r"^'([^']+)' does not depend on any axioms$",
        output,
        flags=re.MULTILINE,
    )
    observed: dict[str, list[str]] = {}
    for name, body in dependencies:
        axioms = [
            item.strip()
            for item in body.replace("\n", " ").split(",")
            if item.strip()
        ]
        observed[name] = axioms
    for name in zero:
        observed[name] = []
    if set(observed) != set(names) or len(observed) != len(names):
        missing = sorted(set(names) - set(observed))
        extra = sorted(set(observed) - set(names))
        raise AuditError(
            f"E058 axiom output mismatch: missing={missing} extra={extra}"
        )
    for name, axioms in observed.items():
        if not set(axioms).issubset(ALLOWED_AXIOMS):
            raise AuditError(f"unexpected axioms for {name}: {axioms}")
    final_axioms = set(observed["Erdos617.e058Problem617AtFive"])
    if final_axioms != ALLOWED_AXIOMS:
        raise AuditError(
            f"final fixed-r=5 theorem axiom set differs: {sorted(final_axioms)}"
        )
    if "sorryAx" in output:
        raise AuditError("fresh E058 axiom audit mentions sorryAx")
    return observed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--lake", type=Path, required=True)
    parser.add_argument("--work-directory", type=Path)
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--require-no-local-build", action="store_true")
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--initial-clean-start-receipt", type=Path)
    args = parser.parse_args()

    runner_path = Path(__file__).resolve()
    runner_sha256 = sha256_path(runner_path)
    repository, lean_root = locate_roots(args.project)
    lake = args.lake.resolve()
    work = (
        args.work_directory.resolve()
        if args.work_directory
        else lean_root / ".e058-audit"
    )
    try:
        work.relative_to(repository)
    except ValueError as error:
        raise AuditError("E058 work directory must be inside the repository") from error
    if (
        args.require_no_local_build
        and not args.resume
        and (lean_root / ".lake/build").exists()
    ):
        raise AuditError("local Lean build directory exists before the E058 audit")
    if work.exists() and any(work.iterdir()) and not args.resume:
        raise AuditError(f"E058 audit work directory is not empty: {work}")
    work.mkdir(parents=True, exist_ok=True)
    clean_start_audit = None
    if args.initial_clean_start_receipt is not None:
        if not args.resume:
            raise AuditError(
                "--initial-clean-start-receipt is valid only with --resume"
            )
        clean_start_audit = validate_clean_start_receipt(
            args.initial_clean_start_receipt.resolve()
        )

    transcript = Transcript(args.log.resolve(), append=args.resume)
    started = time.monotonic()
    try:
        validate_pins(lean_root, lake, transcript)
        base_sources = source_inventory(lean_root)
        validate_forbidden_sources(base_sources, lean_root)
        before = inventory_hashes(base_sources, lean_root)

        environment = dict(os.environ)
        environment["PATH"] = str(lake.parent) + os.pathsep + environment.get(
            "PATH", ""
        )
        environment["E058_LEAN_LAKE"] = str(lake)
        prefix = [str(lake), "--no-ansi"]
        version_output, _ = transcript.run(
            [*prefix, "env", "lean", "--version"],
            cwd=lean_root,
            environment=environment,
            lean_gate=True,
        )
        if (
            "Lean (version 4.32.0" not in version_output
            or f"commit {LEAN_COMMIT}" not in version_output
        ):
            raise AuditError(f"unexpected Lean version: {version_output.strip()}")

        lean_runs: list[dict[str, object]] = []
        cores = work / "cores"
        core_receipt_path = cores / "receipt.json"
        if args.resume:
            if not core_receipt_path.is_file():
                raise AuditError("resume requested without a completed core receipt")
            certificate_paths = (
                lean_root / "Erdos617/Sat/NeighborhoodOrbitCertificate.lean",
                lean_root
                / "Erdos617/Sat/NeighborhoodCrossPatternCertificate.lean",
                lean_root / "Erdos617/Sat/ZeroAnchorOrbitCertificate.lean",
            )
            certificate_hashes = {
                str(path.relative_to(repository)): sha256_path(path)
                for path in certificate_paths
            }
            transcript.note(
                "E058-FRESH-AUDIT-RESUME "
                "phase=post-core-replay reused_local_build=1"
            )
        else:
            certificate_hashes = regenerate_certificates(
                repository=repository,
                lean_root=lean_root,
                work=work,
                transcript=transcript,
                environment=environment,
            )
            for target in ("Erdos617", *LEAN_LIBRARY_TARGETS):
                output, elapsed = transcript.run(
                    [*prefix, "build", target],
                    cwd=lean_root,
                    environment=environment,
                    lean_gate=True,
                )
                lean_runs.append(
                    {
                        "kind": "lake-build",
                        "target": target,
                        "elapsed_seconds": elapsed,
                        "success_marker": (
                            "Build completed successfully" in output
                        ),
                    }
                )
            transcript.run(
                [
                    sys.executable,
                    str(repository / "repro/generate_e058_rup_cores.py"),
                    "--output-directory",
                    str(cores),
                    "--c-checker",
                    str(repository / "build/lrat-check-upstream"),
                    "--python-checker",
                    str(repository / "src/check_lrat.py"),
                ],
                cwd=repository,
                environment=environment,
            )
        core_receipt = validate_core_receipt(core_receipt_path, repository)
        labels = [str(record["label"]) for record in core_receipt["records"]]
        label_set = set(labels)

        units = work / "units"
        unit_manifest_path = work / "unit_manifest.json"
        committed_unit_manifest_path = (
            repository
            / "artifacts/e058_special_brooks_kernel_bridge/unit_manifest.json"
        )
        if args.resume:
            if not unit_manifest_path.is_file() or not units.is_dir():
                raise AuditError(
                    "resume requested without a retained unit manifest"
                )
            with tempfile.TemporaryDirectory(
                prefix="e058-unit-replay-",
                dir=work,
            ) as temporary:
                replay_root = Path(temporary)
                replay_units = replay_root / "units"
                replay_manifest_path = replay_root / "unit_manifest.json"
                transcript.run(
                    [
                        sys.executable,
                        str(repository / "repro/generate_e058_unit_cnfs.py"),
                        "--receipt-directory",
                        str(cores),
                        "--repository",
                        str(repository),
                        "--output-directory",
                        str(replay_units),
                        "--manifest",
                        str(replay_manifest_path),
                    ],
                    cwd=repository,
                    environment=environment,
                )
                validate_unit_manifest(
                    replay_manifest_path,
                    unit_manifest_path,
                    label_set,
                    repository,
                )
            transcript.note(
                "E058-UNIT-CNF-REPLAY-PASS "
                "records=89 retained_manifest_match=1"
            )
        else:
            transcript.run(
                [
                    sys.executable,
                    str(repository / "repro/generate_e058_unit_cnfs.py"),
                    "--receipt-directory",
                    str(cores),
                    "--repository",
                    str(repository),
                    "--output-directory",
                    str(units),
                    "--manifest",
                    str(unit_manifest_path),
                ],
                cwd=repository,
                environment=environment,
            )
        generated_units = validate_unit_manifest(
            unit_manifest_path,
            committed_unit_manifest_path,
            label_set,
            repository,
        )
        generated_unit_records = {
            str(record["label"]): record
            for record in generated_units["records"]
        }
        for record in core_receipt["records"]:
            label = str(record["label"])
            unit = generated_unit_records[label]
            source = record["source"]
            if (
                unit["source_raw_sha256"] != source["cnf_raw_sha256"]
                or unit["source_variables"] != source["variables"]
                or unit["source_clauses"] != source["original_clauses"]
            ):
                raise AuditError(
                    f"E058 unit/source provenance mismatch for {label}"
                )

        kernel_source = lean_root / "generated/e058_fresh_kernel"
        kernel_work = work / "kernel"
        transcript.run(
            [
                sys.executable,
                str(repository / "repro/run_e058_lean_kernel_imports.py"),
                "--core-directory",
                str(cores),
                "--work-directory",
                str(kernel_work),
                "--source-directory",
                str(kernel_source),
                "--timeout-seconds",
                "1800",
            ],
            cwd=repository,
            environment=environment,
        )
        kernel_receipt_path = kernel_work / "kernel-aggregate-receipt.json"
        kernel_receipt = validate_aggregate(
            kernel_receipt_path,
            verification="LEAN-KERNEL-RUP-UNSAT",
            labels=label_set,
            tools={
                "audit_runner": (
                    repository / "repro/run_e058_lean_kernel_imports.py"
                ),
                "module_generator": (
                    repository / "repro/generate_e058_lean_stage_modules.py"
                ),
                "stage_splitter": (
                    repository / "src/split_rup_lrat_stages.py"
                ),
            },
        )
        scan_logs_for_warnings(kernel_work)

        semantic_source = lean_root / "generated/e058_fresh_semantic"
        semantic_work = work / "semantic"
        transcript.run(
            [
                sys.executable,
                str(repository / "repro/run_e058_lean_semantic_closures.py"),
                "--core-directory",
                str(cores),
                "--unit-manifest",
                str(unit_manifest_path),
                "--kernel-receipt-root",
                str(kernel_work),
                "--source-directory",
                str(semantic_source),
                "--work-directory",
                str(semantic_work),
                "--timeout-seconds",
                "1800",
                "--memory-megabytes",
                "12288",
            ],
            cwd=repository,
            environment=environment,
        )
        semantic_receipt_path = (
            semantic_work / "semantic-aggregate-receipt.json"
        )
        semantic_receipt = validate_aggregate(
            semantic_receipt_path,
            verification="LEAN-KERNEL-CONDITIONAL-GRAPH-UNSAT",
            labels=label_set,
            tools={
                "audit_runner": (
                    repository / "repro/run_e058_lean_semantic_closures.py"
                )
            },
        )
        scan_logs_for_warnings(semantic_work)

        olean_root = lean_root / ".lake/build/lib/lean"
        olean_root.mkdir(parents=True, exist_ok=True)
        for module in COVERAGE_MODULES:
            output, elapsed = transcript.run(
                [
                    *prefix,
                    "env",
                    "lean",
                    "-j1",
                    "-M12288",
                    "-o",
                    str(olean_root / f"{module}.olean"),
                    str(lean_root / f"{module}.lean"),
                ],
                cwd=lean_root,
                environment=environment,
                lean_gate=True,
            )
            lean_runs.append(
                {
                    "kind": "coverage-compile",
                    "target": module,
                    "elapsed_seconds": elapsed,
                    "output_sha256": hashlib.sha256(
                        output.encode("utf-8")
                    ).hexdigest(),
                    "olean_sha256": sha256_path(
                        olean_root / f"{module}.olean"
                    ),
                }
            )

        audit_text, audit_names = render_axiom_audit(labels)
        audit_source = work / "E058FreshAxiomAudit.lean"
        audit_source.write_text(
            audit_text, encoding="ascii", newline="\n"
        )
        audit_output, audit_elapsed = transcript.run(
            [*prefix, "env", "lean", "-j1", "-M12288", str(audit_source)],
            cwd=lean_root,
            environment=environment,
            lean_gate=True,
        )
        audit_output_path = work / "E058FreshAxiomAudit.out"
        audit_output_path.write_text(
            audit_output, encoding="utf-8", newline="\n"
        )
        observed_axioms = parse_axiom_audit(audit_output, audit_names)

        generated_sources = sorted(
            [*kernel_source.rglob("*.lean"), *semantic_source.rglob("*.lean")]
        )
        validate_forbidden_sources(generated_sources, lean_root)
        after = inventory_hashes(base_sources, lean_root)
        if after != before:
            raise AuditError("audited E058 source bytes changed during the run")
        generated_inventory = inventory_hashes(generated_sources, lean_root)

        elapsed = time.monotonic() - started
        receipt = {
            "schema_version": 1,
            "experiment": "E058-R5-SPECIAL-BROOKS-KERNEL-BRIDGE",
            "verification": "LEAN-KERNEL-FIXED-R5",
            "fresh_local_build": bool(
                args.require_no_local_build and not args.resume
            ),
            "resumed_after_core_replay": bool(args.resume),
            "clean_start_audit": clean_start_audit,
            "lean": "4.32.0",
            "lean_commit": LEAN_COMMIT,
            "mathlib": MATHLIB_REVISION,
            "lake_manifest_sha256": LAKE_MANIFEST_SHA256,
            "toolchain_binary_sha256": {
                "lake": sha256_path(lake),
                "lean": sha256_path(lake.parent / "lean"),
            },
            "audit_runner": {
                "path": str(runner_path.relative_to(repository)),
                "sha256_at_start": runner_sha256,
            },
            "tool_sha256": {
                "core_generator": sha256_path(
                    repository / "repro/generate_e058_rup_cores.py"
                ),
                "cross_pattern_generator": sha256_path(
                    repository
                    / "repro/generate_e058_cross_pattern_certificate.py"
                ),
                "kernel_import_runner": sha256_path(
                    repository / "repro/run_e058_lean_kernel_imports.py"
                ),
                "module_generator": sha256_path(
                    repository / "repro/generate_e058_lean_stage_modules.py"
                ),
                "neighborhood_orbit_generator": sha256_path(
                    repository
                    / "repro/generate_e058_neighborhood_orbit_certificate.py"
                ),
                "semantic_closure_runner": sha256_path(
                    repository / "repro/run_e058_lean_semantic_closures.py"
                ),
                "stage_splitter": sha256_path(
                    repository / "src/split_rup_lrat_stages.py"
                ),
                "unit_generator": sha256_path(
                    repository / "repro/generate_e058_unit_cnfs.py"
                ),
                "zero_anchor_orbit_generator": sha256_path(
                    repository
                    / "repro/generate_e058_zero_anchor_orbit_certificate.py"
                ),
            },
            "cores": {
                "count": EXPECTED_LABELS,
                "receipt_sha256": sha256_path(core_receipt_path),
                "rup_only": True,
                "c_checks": EXPECTED_LABELS,
                "python_checks": EXPECTED_LABELS,
                "negative_checks": 4 * EXPECTED_LABELS,
                "tool_sha256": core_receipt["tool_sha256"],
            },
            "unit_manifest": {
                "count": EXPECTED_LABELS,
                "generated_sha256": sha256_path(unit_manifest_path),
                "committed_sha256": sha256_path(
                    committed_unit_manifest_path
                ),
                "source_extraction_replayed": True,
            },
            "kernel_imports": {
                "count": EXPECTED_LABELS,
                "receipt_sha256": sha256_path(kernel_receipt_path),
                "allowed_axioms": ["propext"],
                "tool_sha256": kernel_receipt["tool_sha256"],
            },
            "semantic_closures": {
                "count": EXPECTED_LABELS,
                "receipt_sha256": sha256_path(semantic_receipt_path),
                "allowed_axioms": sorted(ALLOWED_AXIOMS),
                "tool_sha256": semantic_receipt["tool_sha256"],
            },
            "certificates": certificate_hashes,
            "source_inventory": {
                "count": len(before),
                "combined_sha256": combined_inventory_sha256(before),
                "records": before,
            },
            "generated_source_inventory": {
                "count": len(generated_inventory),
                "combined_sha256": combined_inventory_sha256(
                    generated_inventory
                ),
                "records": generated_inventory,
            },
            "coverage_modules": list(COVERAGE_MODULES),
            "axiom_queries": {
                "count": len(audit_names),
                "allowed_axioms": sorted(ALLOWED_AXIOMS),
                "final_theorem": "Erdos617.e058Problem617AtFive",
                "final_axioms": observed_axioms[
                    "Erdos617.e058Problem617AtFive"
                ],
                "source_sha256": sha256_path(audit_source),
                "output_sha256": sha256_path(audit_output_path),
                "elapsed_seconds": audit_elapsed,
            },
            "lean_runs": lean_runs,
            "warnings": 0,
            "forbidden_source_hits": 0,
            "elapsed_seconds": elapsed,
        }
        receipt_path = work / "fresh-audit-receipt.json"
        write_json(receipt_path, receipt)
        transcript.note(
            "E058-FRESH-LEAN-AUDIT-PASS "
            f"cores={EXPECTED_LABELS} kernel_imports={EXPECTED_LABELS} "
            f"semantic_closures={EXPECTED_LABELS} "
            f"axiom_queries={len(audit_names)} warnings=0 "
            "forbidden_hits=0 "
            f"receipt_sha256={sha256_path(receipt_path)}"
        )
    finally:
        transcript.close()
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (
        AuditError,
        json.JSONDecodeError,
        KeyError,
        OSError,
        StopIteration,
        subprocess.SubprocessError,
        ValueError,
    ) as error:
        raise SystemExit(f"E058-FRESH-LEAN-AUDIT-FAILED: {error}") from error

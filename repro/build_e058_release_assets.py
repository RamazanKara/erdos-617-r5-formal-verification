#!/usr/bin/env python3
"""Build deterministic, reviewable E058 release assets.

The three archives are overlays with the same top-level directory.  Extracting
all of them produces the complete fixed-r=5 verification snapshot without the
multi-gigabyte historical experiments that are unrelated to E058.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import lzma
import shutil
import tarfile
from pathlib import Path

ARCHIVE_ROOT = Path("erdos617-r5-formal-verification")
SOURCE_DATE_EPOCH = 1_784_851_200

CERTIFICATE_TREES = (
    "artifacts/e038_brooks_branches",
    "artifacts/e042_branch19_cross_patterns",
    "artifacts/e043_branch19_zero_neighborhoods",
    "artifacts/e045_zero_anchor_quotients",
    "certificates/e038_brooks_branches",
    "certificates/e042_branch19_cross_patterns",
    "certificates/e043_branch19_zero_neighborhoods",
    "certificates/e045_zero_anchor_quotients",
)

EVIDENCE_TREES = (
    "artifacts/e058_special_brooks_kernel_bridge",
)

SOURCE_FILES = (
    ".gitignore",
    "AI_USAGE.md",
    "CLAIMS.md",
    "LICENSE",
    "Makefile",
    "NEXT.md",
    "PUBLICATION_REDACTIONS.md",
    "README.md",
    "RESEARCH_GOAL.md",
    "RELEASE_CHECKLIST_E058.md",
    "RELEASE_NOTES_E058.md",
    "REPRODUCE_E058.md",
    "STATE.md",
    "artifacts/source_hashes.json",
    "docs/external-fixed-cases-intake-2026-07-22.md",
    "docs/e058-red-team-audit.md",
    "docs/literature.md",
    "docs/problem-spec.md",
    "docs/proof-obligations.md",
    "docs/verification-policy.md",
    "experiments/E033-external-fixed-cases-audit-result.md",
    "experiments/E038-r5-brooks-exterior-pattern-symmetry-result.md",
    "experiments/E042-r5-brooks-branch19-cross-pattern-result.md",
    "experiments/E043-r5-brooks-zero-pattern-neighborhood-result.md",
    "experiments/E045-r5-brooks-zero-anchor-quotient-result.md",
    "experiments/E058-r5-special-brooks-kernel-bridge-plan.md",
    "experiments/E058-r5-special-brooks-kernel-bridge-result.md",
    "experiments/manifest.json",
    "formal/README.md",
    "formal/lean/Erdos617.lean",
    "formal/lean/lake-manifest.json",
    "formal/lean/lakefile.toml",
    "formal/lean/lean-toolchain",
    "paper/Makefile",
    "paper/README.md",
    "paper/erdos617-r5-formal-verification.pdf",
    "paper/main.tex",
    "paper/references.bib",
    "src/check_lrat.py",
    "src/minimize_rup_lrat.py",
    "src/split_rup_lrat_stages.py",
    "tests/test_e058_lean_semantic_closures.py",
    "tests/test_e058_neighborhood_orbit_certificate.py",
    "tests/test_e058_audit_runner.py",
    "tests/test_minimize_rup_lrat.py",
    "tests/test_rup_lrat_stages.py",
    "third_party/drat-trim/LICENSE",
    "third_party/drat-trim/README.md",
    "third_party/drat-trim/lrat-check.c",
)

EVIDENCE_FILES: tuple[str, ...] = ()


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def require_files(repository: Path, relative_paths: set[Path]) -> list[Path]:
    missing = [
        str(relative)
        for relative in sorted(relative_paths)
        if not (repository / relative).is_file()
    ]
    if missing:
        raise FileNotFoundError("required release files are missing: " + ", ".join(missing))
    return sorted(relative_paths)


def tree_files(repository: Path, relative_tree: str) -> set[Path]:
    root = repository / relative_tree
    if not root.is_dir():
        raise FileNotFoundError(f"required release tree is missing: {relative_tree}")
    files = {
        path.relative_to(repository)
        for path in root.rglob("*")
        if path.is_file()
    }
    if not files:
        raise FileNotFoundError(f"required release tree is empty: {relative_tree}")
    return files


def source_inventory(repository: Path) -> list[Path]:
    result = {Path(path) for path in SOURCE_FILES}
    result.update(
        path.relative_to(repository)
        for path in (repository / "formal/lean/Erdos617").rglob("*.lean")
    )
    result.update(
        path.relative_to(repository)
        for path in (repository / "formal/lean").glob("E058*.lean")
    )
    for tree in (
        "formal/lean/generated/e058_fresh_kernel",
        "formal/lean/generated/e058_fresh_semantic",
    ):
        root = repository / tree
        generated_sources = {
            path.relative_to(repository)
            for path in root.rglob("*.lean")
            if path.is_file()
        }
        if not generated_sources:
            raise FileNotFoundError(
                f"required generated Lean source tree is empty: {tree}"
            )
        result.update(generated_sources)
    result.update(
        path.relative_to(repository)
        for path in (repository / "repro").glob("*e058*.py")
    )
    # The E058 generators share the generic CNF class and several helpers whose
    # filenames do not contain "brooks".  Keep the small Python support tree
    # complete so an extracted source asset can really regenerate every input.
    result.update(
        path.relative_to(repository)
        for path in (repository / "src").glob("*.py")
    )
    return require_files(repository, result)


def certificate_inventory(repository: Path) -> list[Path]:
    result: set[Path] = set()
    for tree in CERTIFICATE_TREES:
        result.update(tree_files(repository, tree))
    return require_files(repository, result)


def evidence_inventory(repository: Path) -> list[Path]:
    result = {Path(path) for path in EVIDENCE_FILES}
    for tree in EVIDENCE_TREES:
        result.update(tree_files(repository, tree))
    return require_files(repository, result)


def build_archive(
    repository: Path,
    output: Path,
    relative_paths: list[Path],
) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("wb") as raw_stream:
        with lzma.LZMAFile(
            raw_stream,
            mode="wb",
            format=lzma.FORMAT_XZ,
            check=lzma.CHECK_CRC64,
            preset=6,
        ) as compressed:
            with tarfile.open(
                fileobj=compressed,
                mode="w",
                format=tarfile.GNU_FORMAT,
            ) as archive:
                for relative in relative_paths:
                    source = repository / relative
                    data = source.read_bytes()
                    member = tarfile.TarInfo(str(ARCHIVE_ROOT / relative))
                    member.size = len(data)
                    member.mtime = SOURCE_DATE_EPOCH
                    member.uid = 0
                    member.gid = 0
                    member.uname = ""
                    member.gname = ""
                    # The repository was migrated from a Windows-mounted
                    # filesystem, where executable bits are not meaningful
                    # and many ordinary text files appear executable.  Make
                    # archive modes content-deterministic instead.
                    member.mode = 0o755 if data.startswith(b"#!") else 0o644
                    archive.addfile(member, io.BytesIO(data))


def write_asset_hashes(output_directory: Path, assets: list[Path]) -> Path:
    inventory = output_directory / "SHA256SUMS"
    lines = [
        f"{sha256_path(asset)}  {asset.name}"
        for asset in sorted(assets, key=lambda path: path.name)
    ]
    inventory.write_text("\n".join(lines) + "\n", encoding="ascii", newline="\n")
    return inventory


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", type=Path, default=Path.cwd())
    parser.add_argument("--output-directory", type=Path, required=True)
    args = parser.parse_args()

    repository = args.repository.resolve()
    output_directory = args.output_directory.resolve()
    output_directory.mkdir(parents=True, exist_ok=True)
    if any(output_directory.iterdir()):
        raise FileExistsError(
            f"release output directory is not empty: {output_directory}"
        )

    assets = [
        output_directory / "erdos617-r5-source.tar.xz",
        output_directory / "erdos617-r5-certificates.tar.xz",
        output_directory / "erdos617-r5-audit-evidence.tar.xz",
    ]
    inventories = (
        source_inventory(repository),
        certificate_inventory(repository),
        evidence_inventory(repository),
    )
    inventory_sets = [set(inventory) for inventory in inventories]
    overlaps = (
        inventory_sets[0] & inventory_sets[1],
        inventory_sets[0] & inventory_sets[2],
        inventory_sets[1] & inventory_sets[2],
    )
    if any(overlaps):
        examples = sorted(str(path) for overlap in overlaps for path in overlap)
        raise ValueError(
            "release archive inventories overlap: " + ", ".join(examples[:20])
        )
    for asset, inventory in zip(assets, inventories, strict=True):
        build_archive(repository, asset, inventory)
        print(
            f"E058-RELEASE-ASSET-PASS path={asset.name} "
            f"files={len(inventory)} bytes={asset.stat().st_size} "
            f"sha256={sha256_path(asset)}"
        )

    paper = output_directory / "erdos617-r5-formal-verification.pdf"
    shutil.copyfile(
        repository / "paper/erdos617-r5-formal-verification.pdf",
        paper,
    )
    assets.append(paper)
    hashes = write_asset_hashes(output_directory, assets)
    print(
        f"E058-RELEASE-HASHES-PASS assets={len(assets)} "
        f"sha256={sha256_path(hashes)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

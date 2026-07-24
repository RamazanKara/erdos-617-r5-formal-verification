#!/usr/bin/env python3
"""Write the exact inner SHA-256 inventory for the E058 release overlay."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPOSITORY_ROOT))

from repro.build_e058_release_assets import (
    certificate_inventory,
    evidence_inventory,
    sha256_path,
    source_inventory,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", type=Path, default=Path.cwd())
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(
            "artifacts/e058_special_brooks_kernel_bridge/SHA256SUMS"
        ),
    )
    args = parser.parse_args()

    repository = args.repository.resolve()
    output = (
        args.output.resolve()
        if args.output.is_absolute()
        else (repository / args.output).resolve()
    )
    try:
        output_relative = output.relative_to(repository)
    except ValueError as error:
        raise ValueError("scoped hash inventory must be inside the repository") from error

    paths = {
        *source_inventory(repository),
        *certificate_inventory(repository),
        *evidence_inventory(repository),
    }
    paths.discard(output_relative)
    lines = [
        f"{sha256_path(repository / relative)}  {relative}"
        for relative in sorted(paths)
    ]
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines) + "\n", encoding="ascii", newline="\n")
    print(
        "E058-SCOPED-HASHES-PASS "
        f"files={len(paths)} sha256={sha256_path(output)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Generate the transparent E043 zero-anchor orbit certificate.

For each of the three residual E042 parents, the only finite choice is which
nonzero exterior-row classes are adjacent to the zero-pattern anchor.  There
are at most six such rows.  The emitted Lean theorems exhaust all Boolean
masks and check the cross-pattern stabilizer action with ordinary `decide`.
"""

from __future__ import annotations

import argparse
import itertools
import sys
from collections import Counter
from functools import cache
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from generate_r5_brooks_zero_pattern_neighborhood_cnf import (
    OPEN_PARENTS,
    image_subset,
    neighbor_subset_representatives,
    pattern_vertices,
    permute_pattern,
)


def lean_vector(values: tuple[int, ...]) -> str:
    chunks = [
        ", ".join(map(str, values[index : index + 12]))
        for index in range(0, len(values), 12)
    ]
    return "![" + ",\n    ".join(chunks) + "]"


def inverse(permutation: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(permutation.index(value) for value in range(len(permutation)))


def reverse_five_bits(pattern: int) -> int:
    """Match r5ExteriorPatternCode's weights 16,8,4,2,1."""
    return sum(
        ((pattern >> index) & 1) << (4 - index)
        for index in range(5)
    )


@cache
def cached_pattern_vertices(
    parent: int,
) -> tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...]]:
    return pattern_vertices(parent)


@cache
def cached_representatives(parent: int) -> tuple[int, ...]:
    return neighbor_subset_representatives(parent)


@cache
def stabilizer_pairs(
    parent: int,
) -> tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]:
    _, _, patterns = cached_pattern_vertices(parent)
    pairs: set[tuple[tuple[int, ...], tuple[int, ...]]] = set()
    for column_permutation in itertools.permutations(range(4)):
        transformed = tuple(
            permute_pattern(pattern, column_permutation)
            for pattern in patterns
        )
        if Counter(transformed) != Counter(patterns):
            continue
        choices = tuple(
            tuple(
                index
                for index, target in enumerate(patterns)
                if target == pattern
            )
            for pattern in transformed
        )
        for action in itertools.product(*choices):
            if len(set(action)) == len(patterns):
                pairs.add((column_permutation, tuple(action)))
    return tuple(sorted(pairs))


def witness(parent: int, mask: int) -> tuple[int, int]:
    representatives = cached_representatives(parent)
    for witness_index, (_, action) in enumerate(stabilizer_pairs(parent)):
        transformed = image_subset(mask, action)
        if transformed in representatives:
            return representatives.index(transformed), witness_index
    raise AssertionError(f"parent {parent}: unclassified mask {mask}")


def render_parent(parent: int) -> str:
    _, nonzero_vertices, patterns = cached_pattern_vertices(parent)
    size = len(patterns)
    nonzero_start = nonzero_vertices[0]
    if nonzero_vertices != tuple(range(nonzero_start, 26)):
        raise AssertionError(f"parent {parent}: nonzero rows are not a final interval")
    pairs = stabilizer_pairs(parent)
    representatives = cached_representatives(parent)
    tag = f"P{parent:02d}"
    column_maps = "\n".join(
        f"  | {index} => {lean_vector(column)}"
        for index, (column, _) in enumerate(pairs)
    )
    column_inverses = "\n".join(
        f"  | {index} => {lean_vector(inverse(column))}"
        for index, (column, _) in enumerate(pairs)
    )
    row_maps = "\n".join(
        f"  | {index} => {lean_vector(action)}"
        for index, (_, action) in enumerate(pairs)
    )
    row_inverses = "\n".join(
        f"  | {index} => {lean_vector(inverse(action))}"
        for index, (_, action) in enumerate(pairs)
    )
    pattern_vector = lean_vector(
        tuple(reverse_five_bits(pattern) for pattern in patterns)
    )
    representative_vector = lean_vector(tuple(representatives))
    witness_rows = []
    for mask in range(1 << size):
        if mask.bit_count() <= 5:
            child, witness_index = witness(parent, mask)
        else:
            child, witness_index = 0, 0
        witness_rows.append((child, witness_index))
    child_vector = lean_vector(tuple(row[0] for row in witness_rows))
    action_vector = lean_vector(tuple(row[1] for row in witness_rows))
    return f"""
def r5ZeroAnchor{tag}ColumnMap
    (witness : Fin {len(pairs)}) : Fin 4 → Fin 4 :=
  match witness.val with
{column_maps}
  | _ => ![0, 1, 2, 3]

def r5ZeroAnchor{tag}ColumnInverseMap
    (witness : Fin {len(pairs)}) : Fin 4 → Fin 4 :=
  match witness.val with
{column_inverses}
  | _ => ![0, 1, 2, 3]

def r5ZeroAnchor{tag}ColumnPermutation
    (witness : Fin {len(pairs)}) : Equiv.Perm (Fin 4) :=
  {{
    toFun := r5ZeroAnchor{tag}ColumnMap witness
    invFun := r5ZeroAnchor{tag}ColumnInverseMap witness
    left_inv := by
      intro column
      fin_cases witness <;> fin_cases column <;> decide
    right_inv := by
      intro column
      fin_cases witness <;> fin_cases column <;> decide
  }}

def r5ZeroAnchor{tag}RowMap
    (witness : Fin {len(pairs)}) : Fin {size} → Fin {size} :=
  match witness.val with
{row_maps}
  | _ => {lean_vector(tuple(range(size)))}

def r5ZeroAnchor{tag}RowInverseMap
    (witness : Fin {len(pairs)}) : Fin {size} → Fin {size} :=
  match witness.val with
{row_inverses}
  | _ => {lean_vector(tuple(range(size)))}

def r5ZeroAnchor{tag}RowPermutation
    (witness : Fin {len(pairs)}) : Equiv.Perm (Fin {size}) :=
  {{
    toFun := r5ZeroAnchor{tag}RowMap witness
    invFun := r5ZeroAnchor{tag}RowInverseMap witness
    left_inv := by
      intro row
      fin_cases witness <;> fin_cases row <;> decide
    right_inv := by
      intro row
      fin_cases witness <;> fin_cases row <;> decide
  }}

def r5ZeroAnchor{tag}ActionMap
    (witness : Fin {len(pairs)}) (vertex : Fin 26) : Fin 26 :=
  if hcolumn :
      1 ≤ (vertex : Nat) ∧ (vertex : Nat) < 5 then
    ⟨(r5ZeroAnchor{tag}ColumnInverseMap witness
        ⟨(vertex : Nat) - 1, by omega⟩ : Nat) + 1,
      by omega⟩
  else if hrow : {nonzero_start} ≤ (vertex : Nat) then
    ⟨(r5ZeroAnchor{tag}RowInverseMap witness
        ⟨(vertex : Nat) - {nonzero_start}, by omega⟩ : Nat) +
        {nonzero_start},
      by omega⟩
  else
    vertex

def r5ZeroAnchor{tag}ActionInverseMap
    (witness : Fin {len(pairs)}) (vertex : Fin 26) : Fin 26 :=
  if hcolumn :
      1 ≤ (vertex : Nat) ∧ (vertex : Nat) < 5 then
    ⟨(r5ZeroAnchor{tag}ColumnMap witness
        ⟨(vertex : Nat) - 1, by omega⟩ : Nat) + 1,
      by omega⟩
  else if hrow : {nonzero_start} ≤ (vertex : Nat) then
    ⟨(r5ZeroAnchor{tag}RowMap witness
        ⟨(vertex : Nat) - {nonzero_start}, by omega⟩ : Nat) +
        {nonzero_start},
      by omega⟩
  else
    vertex

def r5ZeroAnchor{tag}ActionRelabeling
    (witness : Fin {len(pairs)}) : Equiv.Perm (Fin 26) :=
  {{
    toFun := r5ZeroAnchor{tag}ActionMap witness
    invFun := r5ZeroAnchor{tag}ActionInverseMap witness
    left_inv := by
      intro vertex
      fin_cases witness <;> fin_cases vertex <;> decide
    right_inv := by
      intro vertex
      fin_cases witness <;> fin_cases vertex <;> decide
  }}

def r5ZeroAnchor{tag}Pattern : Fin {size} → Nat :=
  {pattern_vector}

def r5ZeroAnchor{tag}TransformedPattern
    (row : Fin {size}) (witness : Fin {len(pairs)}) : Nat :=
  (∑ column : Fin 4,
    edgeBit
        (Nat.testBit (r5ZeroAnchor{tag}Pattern row)
          (4 - (column : Nat))) *
      2 ^ (4 -
        (r5ZeroAnchor{tag}ColumnMap witness column : Nat))) +
    edgeBit (Nat.testBit (r5ZeroAnchor{tag}Pattern row) 0)

theorem r5ZeroAnchor{tag}Pattern_stabilizer :
    ∀ witness row,
      r5ZeroAnchor{tag}TransformedPattern row witness =
        r5ZeroAnchor{tag}Pattern
          (r5ZeroAnchor{tag}RowMap witness row) := by
  decide

def r5ZeroAnchor{tag}Representative : Fin {len(representatives)} → Nat :=
  {representative_vector}

def r5ZeroAnchor{tag}RepresentativeWeight
    (child : Fin {len(representatives)}) : Nat :=
  ∑ index : Fin {size},
    edgeBit
      (Nat.testBit (r5ZeroAnchor{tag}Representative child)
        (index : Nat))

theorem r5ZeroAnchor{tag}RepresentativeWeight_le_five :
    ∀ child, r5ZeroAnchor{tag}RepresentativeWeight child ≤ 5 := by
  decide

def r5ZeroAnchor{tag}Mask (bits : Fin {size} → Bool) : Nat :=
  ∑ index, edgeBit (bits index) * 2 ^ (index : Nat)

def r5ZeroAnchor{tag}TransformedMask
    (bits : Fin {size} → Bool) (witness : Fin {len(pairs)}) : Nat :=
  ∑ index, edgeBit (bits index) *
    2 ^ (r5ZeroAnchor{tag}RowMap witness index : Nat)

def r5ZeroAnchor{tag}TransformedBits
    (bits : Fin {size} → Bool) (witness : Fin {len(pairs)}) :
    Fin {size} → Bool :=
  fun index =>
    bits (r5ZeroAnchor{tag}RowInverseMap witness index)

theorem r5ZeroAnchor{tag}Mask_lt :
    ∀ bits : Fin {size} → Bool,
      r5ZeroAnchor{tag}Mask bits < 2 ^ {size} := by
  decide

def r5ZeroAnchor{tag}WitnessChild
    (bits : Fin {size} → Bool) : Fin {len(representatives)} :=
  ({child_vector})
    ⟨r5ZeroAnchor{tag}Mask bits,
      r5ZeroAnchor{tag}Mask_lt bits⟩

def r5ZeroAnchor{tag}WitnessAction
    (bits : Fin {size} → Bool) : Fin {len(pairs)} :=
  ({action_vector})
    ⟨r5ZeroAnchor{tag}Mask bits,
      r5ZeroAnchor{tag}Mask_lt bits⟩

set_option maxRecDepth 10000 in
theorem r5_zero_anchor_{parent:02d}_orbit_check :
    ∀ bits : Fin {size} → Bool,
      (∑ index, edgeBit (bits index)) ≤ 5 →
      r5ZeroAnchor{tag}TransformedMask bits
          (r5ZeroAnchor{tag}WitnessAction bits) =
      r5ZeroAnchor{tag}Representative
          (r5ZeroAnchor{tag}WitnessChild bits) := by
  decide

set_option maxRecDepth 10000 in
theorem r5_zero_anchor_{parent:02d}_orbit_bits_check :
    ∀ bits : Fin {size} → Bool,
      (∑ index, edgeBit (bits index)) ≤ 5 →
      ∀ index,
        r5ZeroAnchor{tag}TransformedBits bits
            (r5ZeroAnchor{tag}WitnessAction bits) index =
          Nat.testBit
            (r5ZeroAnchor{tag}Representative
              (r5ZeroAnchor{tag}WitnessChild bits))
            (index : Nat) := by
  decide
"""


def render() -> str:
    sections = "\n".join(render_parent(parent) for parent in OPEN_PARENTS)
    return f"""/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Sat.SpecialBrooksCoverage

/-!
# Generated zero-anchor orbit certificates for E043

Generated by `repro/generate_e058_zero_anchor_orbit_certificate.py`.
The three theorems exhaust at most 64 Boolean masks each.
-/

@[expose] public section

open Finset Fintype
open scoped BigOperators

namespace Erdos617
{sections}
end Erdos617
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    for parent in OPEN_PARENTS:
        pairs = stabilizer_pairs(parent)
        if not pairs:
            raise AssertionError(f"parent {parent}: empty stabilizer")
        size = len(cached_pattern_vertices(parent)[2])
        valid = sum(mask.bit_count() <= 5 for mask in range(1 << size))
        for mask in range(1 << size):
            if mask.bit_count() <= 5:
                witness(parent, mask)
        print(
            "E058-ZERO-ANCHOR-ORBIT-PARENT-PASS "
            f"parent={parent:02d} rows={size} valid_masks={valid} "
            f"actions={len(pairs)} "
            f"children={len(cached_representatives(parent))}"
        )
    source = render()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(source, encoding="utf-8", newline="\n")
    print(
        "E058-ZERO-ANCHOR-ORBIT-CERTIFICATE-PASS "
        f"bytes={len(source.encode('utf-8'))}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

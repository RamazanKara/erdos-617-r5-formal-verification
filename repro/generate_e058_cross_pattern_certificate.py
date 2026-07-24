#!/usr/bin/env python3
"""Generate the transparent E058 branch-19 cross-pattern certificate.

The proof is a pruned equality decision tree on the eight exterior stubs of
the K4-plus-isolate neighborhood.  The last four stubs belong to the isolated
neighbor and are required to have distinct endpoints.  Consequently the tree
has only 799 leaves.  Every leaf is closed by simplification, so the emitted
Lean theorem is checked by the ordinary kernel and uses no native evaluator.
"""

from __future__ import annotations

import argparse
import itertools
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from generate_r5_brooks_branch19_cross_pattern_cnf import (
    EXPECTED_REPRESENTATIVES,
    FIFTH_STUBS,
    set_partitions,
    signature,
)


PERMUTATIONS = tuple(itertools.permutations(range(4)))
INVERSE_PERMUTATIONS = tuple(
    tuple(permutation.index(value) for value in range(4))
    for permutation in PERMUTATIONS
)
ISOLATE_STUBS = frozenset(FIFTH_STUBS)


def valid_partitions() -> tuple[tuple[tuple[int, ...], ...], ...]:
    return tuple(
        partition
        for partition in set_partitions(tuple(range(8)))
        if all(
            sum(stub in ISOLATE_STUBS for stub in block) <= 1
            for block in partition
        )
    )


def witness(partition: tuple[tuple[int, ...], ...]) -> tuple[int, int]:
    for permutation_index, permutation in enumerate(PERMUTATIONS):
        transformed = signature(partition, permutation)
        for child, representative in enumerate(EXPECTED_REPRESENTATIVES):
            if transformed == representative:
                return child, permutation_index
    raise AssertionError(f"unclassified valid partition: {partition}")


def lean_vector(values: tuple[int, ...]) -> str:
    return "![" + ", ".join(map(str, values)) + "]"


def reverse_five_bits(value: int) -> int:
    return sum(
        ((value >> position) & 1) << (4 - position)
        for position in range(5)
    )


def render_tree(
    *,
    next_stub: int,
    blocks: tuple[tuple[int, ...], ...],
    indent: str,
) -> list[str]:
    if next_stub == 8:
        child, permutation = witness(blocks)
        pairs = list(itertools.combinations(range(8), 2))
        relations = {
            (left, right): (
                "="
                if any(left in block and right in block for block in blocks)
                else "≠"
            )
            for left, right in pairs
        }
        lines = [
            f"{indent}refine ⟨{child}, {permutation}, ?_⟩",
            f"{indent}have hpairs :",
        ]
        for index, (left, right) in enumerate(pairs):
            suffix = " ∧" if index + 1 < len(pairs) else " := by"
            lines.append(
                f"{indent}    endpoints {right} "
                f"{relations[left, right]} endpoints {left}{suffix}"
            )
        lines.append(
            f"{indent}  simp_all [R5FifthStubDistinct, eq_comm]"
        )
        lines.append(f"{indent}rcases hpairs with")
        fact_names = [f"hp_{left}_{right}" for left, right in pairs]
        for offset in range(0, len(fact_names), 7):
            chunk = ", ".join(fact_names[offset : offset + 7])
            prefix = "  ⟨" if offset == 0 else "    "
            suffix = "⟩" if offset + 7 >= len(fact_names) else ","
            lines.append(f"{indent}{prefix}{chunk}{suffix}")
        lines.extend(
            [
                f"{indent}simp [r5EndpointPatternMultiset,",
                f"{indent}  r5EndpointPattern, r5StubMask,",
                f"{indent}  r5CrossColumnMap, r5CrossPatternRepresentative,",
                f"{indent}  R5FifthStubDistinct, Finset.filter_singleton,",
                f"{indent}  List.dedup, List.pwFilter,",
                f"{indent}  Fin.sum_univ_succ, eq_comm,",
            ]
        )
        for offset in range(0, len(fact_names), 7):
            chunk = ", ".join(fact_names[offset : offset + 7])
            lines.append(f"{indent}  {chunk},")
        reverse_facts = [
            f"Ne.symm hp_{left}_{right}"
            for left, right in pairs
            if relations[left, right] == "≠"
        ]
        for offset in range(0, len(reverse_facts), 4):
            chunk = ", ".join(reverse_facts[offset : offset + 4])
            suffix = (
                "] <;>"
                if offset + 4 >= len(reverse_facts)
                else ","
            )
            lines.append(f"{indent}  {chunk}{suffix}")
        lines.append(f"{indent}  decide")
        return lines

    result: list[str] = []

    def compare_block(block_index: int, current_indent: str) -> list[str]:
        if block_index == len(blocks):
            return render_tree(
                next_stub=next_stub + 1,
                blocks=blocks + ((next_stub,),),
                indent=current_indent,
            )

        block = blocks[block_index]
        representative = block[0]
        equality_impossible = (
            next_stub in ISOLATE_STUBS
            and any(stub in ISOLATE_STUBS for stub in block)
        )
        if equality_impossible:
            return compare_block(block_index + 1, current_indent)

        equal_blocks = list(blocks)
        equal_blocks[block_index] = block + (next_stub,)
        lines = [
            f"{current_indent}by_cases h{next_stub}_{representative} : "
            f"endpoints {next_stub} = endpoints {representative}",
            f"{current_indent}·",
        ]
        lines.extend(
            render_tree(
                next_stub=next_stub + 1,
                blocks=tuple(equal_blocks),
                indent=current_indent + "  ",
            )
        )
        lines.append(f"{current_indent}·")
        lines.extend(compare_block(block_index + 1, current_indent + "  "))
        return lines

    result.extend(compare_block(0, indent))
    return result


def render() -> str:
    permutations = "\n".join(
        f"  | {index} => {lean_vector(permutation)}"
        for index, permutation in enumerate(PERMUTATIONS)
    )
    inverse_permutations = "\n".join(
        f"  | {index} => {lean_vector(permutation)}"
        for index, permutation in enumerate(INVERSE_PERMUTATIONS)
    )
    representatives = "\n".join(
        f"  | {index} => "
        f"{sorted(reverse_five_bits(value) for value in representative)!r}"
        for index, representative in enumerate(EXPECTED_REPRESENTATIVES)
    )
    sorted_rows = "\n".join(
        f"  | {index} => {lean_vector(tuple([0] * (20 - len(representative)) + sorted(reverse_five_bits(value) for value in representative)))}"
        for index, representative in enumerate(EXPECTED_REPRESENTATIVES)
    )
    tree = "\n".join(
        render_tree(next_stub=1, blocks=((0,),), indent="  ")
    )
    return f"""/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/
module

public import Erdos617.Sat.SpecialBrooksCoverage

/-!
# Generated cross-pattern orbit certificate for E058 branch 19

Generated by `repro/generate_e058_cross_pattern_certificate.py`.
The theorem below checks the complete 799-leaf endpoint-partition tree.
-/

@[expose] public section

open Finset Fintype
open scoped BigOperators

namespace Erdos617

@[simp]
theorem r5_card_filter_fin_zero
    (p : Fin 0 → Prop) [DecidablePred p] :
    #(Finset.univ.filter p) = 0 := by
  simp

@[simp]
theorem r5_card_filter_fin_succ
    (n : Nat) (p : Fin (n + 1) → Prop) [DecidablePred p] :
    #(Finset.univ.filter p) =
      (if p 0 then 1 else 0) +
        #(Finset.univ.filter fun index : Fin n => p index.succ) := by
  calc
    #(Finset.univ.filter p) =
        ∑ index : Fin (n + 1), if p index then 1 else 0 := by
      symm
      simp
    _ = (if p 0 then 1 else 0) +
          ∑ index : Fin n, if p index.succ then 1 else 0 := by
      rw [Fin.sum_univ_succ]
    _ = (if p 0 then 1 else 0) +
          #(Finset.univ.filter fun index : Fin n => p index.succ) := by
      congr 1
      simp

def r5CrossColumnMap (index : Fin 24) : Fin 4 → Fin 4 :=
  match index.val with
{permutations}
  | _ => ![0, 1, 2, 3]

theorem r5CrossColumnMap_bijective :
    ∀ index : Fin 24, Function.Bijective (r5CrossColumnMap index) := by
  decide

def r5CrossColumnInverseMap (index : Fin 24) : Fin 4 → Fin 4 :=
  match index.val with
{inverse_permutations}
  | _ => ![0, 1, 2, 3]

def r5CrossColumnPermutation
    (index : Fin 24) : Equiv.Perm (Fin 4) :=
  {{
    toFun := r5CrossColumnMap index
    invFun := r5CrossColumnInverseMap index
    left_inv := by
      intro column
      fin_cases index <;> fin_cases column <;> decide
    right_inv := by
      intro column
      fin_cases index <;> fin_cases column <;> decide
  }}

def r5CrossPatternRepresentative (child : Fin 20) : List Nat :=
  match child.val with
{representatives}
  | _ => []

/-- The exact sorted twenty-row code used by the corresponding E042 child.
The code weights positions `0, ..., 4` by `16, 8, 4, 2, 1`, exactly as
`r5ExteriorPatternCode` does. -/
def r5CrossPatternSortedCode (child : Fin 20) : Fin 20 → Nat :=
  match child.val with
{sorted_rows}
  | _ => ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem r5CrossPatternSortedCode_monotone (child : Fin 20) :
    Monotone (r5CrossPatternSortedCode child) := by
  fin_cases child <;> decide

theorem r5CrossPatternSortedCode_multiset (child : Fin 20) :
    (List.ofFn (r5CrossPatternSortedCode child) : Multiset Nat) =
      Multiset.replicate
        (20 - (r5CrossPatternRepresentative child).length) 0 +
      (r5CrossPatternRepresentative child : Multiset Nat) := by
  fin_cases child <;> decide

def R5FifthStubDistinct (endpoints : Fin 8 → Fin 26) : Prop :=
  endpoints 4 ≠ endpoints 5 ∧
  endpoints 4 ≠ endpoints 6 ∧
  endpoints 4 ≠ endpoints 7 ∧
  endpoints 5 ≠ endpoints 6 ∧
  endpoints 5 ≠ endpoints 7 ∧
  endpoints 6 ≠ endpoints 7

def r5StubMask (permutation : Fin 24) (stub : Fin 8) : Nat :=
  if hstub : (stub : Nat) < 4 then
    2 ^ (4 - (r5CrossColumnMap permutation ⟨stub, hstub⟩ : Nat))
  else
    1

def r5EndpointPattern
    (endpoints : Fin 8 → Fin 26) (permutation : Fin 24)
    (endpoint : Fin 26) : Nat :=
  ∑ stub, if endpoints stub = endpoint then
    r5StubMask permutation stub else 0

def r5EndpointPatternMultiset
    (endpoints : Fin 8 → Fin 26) (permutation : Fin 24) :
    Multiset Nat :=
  (Finset.univ.image endpoints).val.map
    (r5EndpointPattern endpoints permutation)

def R5CrossPatternOrbitProperty
    (endpoints : Fin 8 → Fin 26) : Prop :=
  R5FifthStubDistinct endpoints →
    ∃ child : Fin 20, ∃ permutation : Fin 24,
      r5EndpointPatternMultiset endpoints permutation =
        (r5CrossPatternRepresentative child : Multiset Nat)

set_option linter.style.maxHeartbeats false in
set_option linter.style.longLine false in
set_option linter.style.cdot false in
set_option linter.flexible false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
set_option linter.unusedSimpArgs false in
set_option linter.unnecessarySeqFocus false in
theorem r5_cross_pattern_orbit_check :
    ∀ endpoints : Fin 8 → Fin 26,
      R5CrossPatternOrbitProperty endpoints := by
  intro endpoints hdistinct
{tree}

end Erdos617
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    partitions = valid_partitions()
    if len(partitions) != 799:
        raise AssertionError("valid partition count changed")
    source = render()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(source, encoding="utf-8", newline="\n")
    print(
        "E058-CROSS-PATTERN-CERTIFICATE-PASS "
        f"partitions={len(partitions)} children={len(EXPECTED_REPRESENTATIVES)} "
        f"permutations={len(PERMUTATIONS)} bytes={len(source.encode('utf-8'))}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

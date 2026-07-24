/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/

import Erdos617.Sat.LRATReify
import Erdos617.Sat.ClauseSemantics

/-!
# Graph specialization of a reified special-Brooks core

The command in this file applies a reified LRAT theorem to the transparent
graph propositions in the exact DIMACS allocation order.  Its result is an
ordinary theorem, quantified over a graph and its decidable adjacency
relation, asserting that one retained input clause is falsified.
-/

open Lean Elab Command

namespace Erdos617.R5Reify

inductive ComparisonScheme
  | fullExterior
  | zeroAnchor

def comparisonPairs : ComparisonScheme → Array (Nat × Nat)
  | .fullExterior =>
      (Array.range 19).map fun offset => (offset + 6, offset + 7)
  | .zeroAnchor =>
      ((Array.range 4).map fun offset => (offset + 7, offset + 8)) ++
      ((Array.range 13).map fun offset => (offset + 12, offset + 13))

def variableNameExprs (scheme : ComparisonScheme) : Array Expr := Id.run do
  let mut names := #[]
  for left in [:26] do
    for offset in [:(25 - left)] do
      names := names.push <|
        mkApp2 (mkConst ``R5VariableName.edge)
          (mkRawNatLit left) (mkRawNatLit (left + offset + 1))
  for vertex in [:26] do
    for position in [:25] do
      for threshold in [:(min (position + 1) 6)] do
        names := names.push <|
          mkApp3 (mkConst ``R5VariableName.degreeCounter)
            (mkRawNatLit vertex) (mkRawNatLit (position + 1))
            (mkRawNatLit (threshold + 1))
  for (left, right) in comparisonPairs scheme do
    for position in [:5] do
      names := names.push <|
        mkApp3 (mkConst ``R5VariableName.lexPrefix)
          (mkRawNatLit left) (mkRawNatLit right)
          (mkRawNatLit position)
  return names

def specialize (outputName theoremName : Name)
    (scheme : ComparisonScheme) : MetaM Unit := do
  let fin26 := mkApp (mkConst ``Fin) (mkRawNatLit 26)
  let graphType := mkApp (mkConst ``SimpleGraph [.zero]) fin26
  Meta.withLocalDecl `G .default graphType fun graph => do
    let adjacency :=
      mkApp2 (mkConst ``SimpleGraph.Adj [.zero]) fin26 graph
    let instanceType :=
      mkApp3
        (mkConst ``DecidableRel [.succ .zero, .succ .zero])
        fin26 fin26 adjacency
    Meta.withLocalDecl `inst .instImplicit instanceType fun adjacencyInstance => do
      let names := variableNameExprs scheme
      let mut propositions := Array.mkEmpty names.size
      for name in names do
        propositions := propositions.push <|
          mkApp3 (mkConst ``r5InterpretVariable)
            graph adjacencyInstance name
      let theoremExpr := mkConst theoremName
      let valueBody := mkAppN theoremExpr propositions
      let typeBody ← Meta.inferType valueBody
      let value ← Meta.mkLambdaFVars #[graph, adjacencyInstance] valueBody
      let type ← Meta.mkForallFVars #[graph, adjacencyInstance] typeBody
      addDecl <| Declaration.thmDecl {
        name := outputName
        levelParams := []
        type
        value
      }

def namedLiteralListExpr (names : Array Expr)
    (clause : Array Int) : MetaM Expr := do
  let literalType := mkConst ``R5NamedLiteral
  let nil :=
    mkApp (mkConst ``List.nil [.zero]) literalType
  let cons :=
    mkApp (mkConst ``List.cons [.zero]) literalType
  let mut result := nil
  for literal in clause.reverse do
    if literal = 0 then
      throwError "zero literal inside a parsed core clause"
    let variableIndex := literal.natAbs
    if variableIndex = 0 || names.size < variableIndex then
      throwError m!"core literal variable outside allocation: {literal}"
    let name := names[variableIndex - 1]!
    let named :=
      if literal > 0 then
        mkApp (mkConst ``R5NamedLiteral.pos) name
      else
        mkApp (mkConst ``R5NamedLiteral.neg) name
    result := mkApp2 cons named result
  return result

partial def buildNamedFalsification
    (graph adjacencyInstance : Expr) (names : Array Expr)
    (clauses : Array (Array Int)) (start stop : Nat) : MetaM Expr := do
  match stop - start with
  | 0 => throwError "cannot map an empty core"
  | 1 =>
      let clause ← namedLiteralListExpr names clauses[start]!
      return mkApp3 (mkConst ``R5NamedClause.Falsified)
        graph adjacencyInstance clause
  | length =>
      let middle := start + length / 2
      let left ← buildNamedFalsification
        graph adjacencyInstance names clauses start middle
      let right ← buildNamedFalsification
        graph adjacencyInstance names clauses middle stop
      return mkApp2 (mkConst ``Or) left right

def mapCore (outputName theoremName : Name)
    (scheme : ComparisonScheme) (variableCount : Nat)
    (clauses : Array (Array Int)) : MetaM Unit := do
  let names := variableNameExprs scheme
  unless variableCount = names.size do
    throwError m!"core header has {variableCount} variables, expected {names.size}"
  let fin26 := mkApp (mkConst ``Fin) (mkRawNatLit 26)
  let graphType := mkApp (mkConst ``SimpleGraph [.zero]) fin26
  Meta.withLocalDecl `G .default graphType fun graph => do
    let adjacency :=
      mkApp2 (mkConst ``SimpleGraph.Adj [.zero]) fin26 graph
    let instanceType :=
      mkApp3
        (mkConst ``DecidableRel [.succ .zero, .succ .zero])
        fin26 fin26 adjacency
    Meta.withLocalDecl `inst .instImplicit instanceType fun adjacencyInstance => do
      let sourceValue :=
        mkApp2 (mkConst theoremName) graph adjacencyInstance
      let sourceType ← Meta.inferType sourceValue
      let expectedType ← buildNamedFalsification
        graph adjacencyInstance names clauses 0 clauses.size
      unless ← Meta.isDefEq sourceType expectedType do
        throwError "reified graph formula does not match the exact named core"
      let value ← Meta.mkLambdaFVars #[graph, adjacencyInstance] sourceValue
      let type ← Meta.mkForallFVars #[graph, adjacencyInstance] expectedType
      addDecl <| Declaration.thmDecl {
        name := outputName
        levelParams := []
        type
        value
      }

end Erdos617.R5Reify

syntax (name := r5SpecializeReified)
  "r5_specialize_reified " ident ppSpace
    ("full_exterior" <|> "zero_anchor") ppSpace ident : command

syntax (name := r5MapReifiedCore)
  "r5_map_reified_core " ident ppSpace
    ("full_exterior" <|> "zero_anchor") ppSpace ident ppSpace str : command

elab_rules : command
  | `(r5_specialize_reified $output:ident full_exterior $source:ident) => do
      let theoremName ← resolveGlobalConstNoOverload source
      let outputName := (← getCurrNamespace) ++ output.getId
      Command.liftTermElabM do
        Erdos617.R5Reify.specialize outputName theoremName
          .fullExterior
  | `(r5_specialize_reified $output:ident zero_anchor $source:ident) => do
      let theoremName ← resolveGlobalConstNoOverload source
      let outputName := (← getCurrNamespace) ++ output.getId
      Command.liftTermElabM do
        Erdos617.R5Reify.specialize outputName theoremName
          .zeroAnchor
  | `(r5_map_reified_core $output:ident full_exterior
      $source:ident $corePath:str) => do
      let theoremName ← resolveGlobalConstNoOverload source
      let outputName := (← getCurrNamespace) ++ output.getId
      let data ← IO.FS.readFile corePath.getString
      match Mathlib.Tactic.Sat.Parser.parseDimacs
          ⟨data, data.startPos⟩ with
      | Std.Internal.Parsec.ParseResult.error _ error =>
          throwError m!"parse core CNF failed: {error}"
      | Std.Internal.Parsec.ParseResult.success next (variableCount, clauses) =>
          unless next.2.IsAtEnd do
            throwError "trailing core CNF input"
          Command.liftTermElabM do
            Erdos617.R5Reify.mapCore outputName theoremName
              .fullExterior variableCount clauses
  | `(r5_map_reified_core $output:ident zero_anchor
      $source:ident $corePath:str) => do
      let theoremName ← resolveGlobalConstNoOverload source
      let outputName := (← getCurrNamespace) ++ output.getId
      let data ← IO.FS.readFile corePath.getString
      match Mathlib.Tactic.Sat.Parser.parseDimacs
          ⟨data, data.startPos⟩ with
      | Std.Internal.Parsec.ParseResult.error _ error =>
          throwError m!"parse core CNF failed: {error}"
      | Std.Internal.Parsec.ParseResult.success next (variableCount, clauses) =>
          unless next.2.IsAtEnd do
            throwError "trailing core CNF input"
          Command.liftTermElabM do
            Erdos617.R5Reify.mapCore outputName theoremName
              .zeroAnchor variableCount clauses

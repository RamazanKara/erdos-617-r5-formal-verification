/-
Copyright (c) 2026 Erdős 617 verification project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erdős 617 verification project
-/

import Erdos617.Sat.R5Reify

/-!
# Semantic closure of reified special-Brooks cores

`r5_close_reified_core` checks every retained input clause against one of the
transparent semantic lemmas in `ClauseSemantics.lean`, then eliminates the
balanced disjunction exported by the LRAT reifier.  Its output is an ordinary
kernel theorem from the exact graph, sorting, and retained-unit assumptions to
`False`.

The elaborator may classify clauses and assemble proof terms, but it cannot
add an axiom: every generated term is checked by Lean's kernel.  Unknown or
malformed clauses are rejected rather than trusted.
-/

open Lean Elab Command

namespace Erdos617.R5CoreSemantics

inductive VariableDescriptor where
  | edge (left right : Nat)
  | degreeCounter (vertex prefixLength threshold : Nat)
  | lexPrefix (left right position : Nat)
  deriving Inhabited, DecidableEq, BEq, Repr

structure SignedVariable where
  positive : Bool
  descriptor : VariableDescriptor
  deriving DecidableEq, BEq, Repr

def variableDescriptors
    (scheme : R5Reify.ComparisonScheme) : Array VariableDescriptor := Id.run do
  let mut names := #[]
  for left in [:26] do
    for offset in [:(25 - left)] do
      names := names.push <|
        .edge left (left + offset + 1)
  for vertex in [:26] do
    for position in [:25] do
      for threshold in [:(min (position + 1) 6)] do
        names := names.push <|
          .degreeCounter vertex (position + 1) (threshold + 1)
  for (left, right) in R5Reify.comparisonPairs scheme do
    for position in [:5] do
      names := names.push <| .lexPrefix left right position
  return names

def describeClause (descriptors : Array VariableDescriptor)
    (clause : Array Int) : Except String (List SignedVariable) := do
  let mut result := []
  for literal in clause do
    if literal = 0 then
      throw "zero literal inside a parsed core clause"
    let variableIndex := literal.natAbs
    if variableIndex = 0 ∨ descriptors.size < variableIndex then
      throw s!"core literal variable outside allocation: {literal}"
    result := {
      positive := literal > 0
      descriptor := descriptors[variableIndex - 1]!
    } :: result
  return result.reverse

def canonicalEdge (left right : Nat) : VariableDescriptor :=
  if left < right then .edge left right else .edge right left

def incidentEdge (vertex position : Nat) : VariableDescriptor :=
  let other := if position < vertex then position else position + 1
  canonicalEdge vertex other

def natLit (value : Nat) : Expr := mkRawNatLit value

def natLtProof (left right : Nat) : MetaM Expr := do
  let proposition ← Meta.mkLt (natLit left) (natLit right)
  Meta.mkDecideProof proposition

def natLeProof (left right : Nat) : MetaM Expr := do
  let proposition ← Meta.mkLe (natLit left) (natLit right)
  Meta.mkDecideProof proposition

def finExpr (bound value : Nat) : MetaM Expr := do
  let proof ← natLtProof value bound
  return mkApp3 (mkConst ``Fin.mk) (natLit bound) (natLit value) proof

def natPairExpr (left right : Nat) : Expr :=
  mkApp4 (mkConst ``Prod.mk [0, 0])
    (mkConst ``Nat) (mkConst ``Nat) (natLit left) (natLit right)

def listExpr (elementType : Expr) (elements : Array Expr) : Expr := Id.run do
  let nil := mkApp (mkConst ``List.nil [.zero]) elementType
  let cons := mkApp (mkConst ``List.cons [.zero]) elementType
  let mut result := nil
  for element in elements.reverse do
    result := mkApp2 cons element result
  return result

def finListExpr (vertices : List Nat) : MetaM Expr := do
  let fin26 := mkApp (mkConst ``Fin) (natLit 26)
  let mut elements := Array.mkEmpty vertices.length
  for vertex in vertices do
    elements := elements.push (← finExpr 26 vertex)
  return listExpr fin26 elements

def comparisonListExpr
    (scheme : R5Reify.ComparisonScheme) : Expr :=
  let natPair := mkApp2 (mkConst ``Prod [0, 0])
    (mkConst ``Nat) (mkConst ``Nat)
  listExpr natPair <|
    (R5Reify.comparisonPairs scheme).map fun pair =>
      natPairExpr pair.1 pair.2

def stripDimacsComments (data : String) : String :=
  String.intercalate "\n" <|
    (data.splitOn "\n").filter fun line =>
      !(line.startsWith "c")

def namedLiteralExpr (names : Array Expr) (literal : Int) : MetaM Expr := do
  if literal = 0 then
    throwError "zero literal inside a parsed core clause"
  let variableIndex := literal.natAbs
  if variableIndex = 0 ∨ names.size < variableIndex then
    throwError m!"core literal variable outside allocation: {literal}"
  let name := names[variableIndex - 1]!
  return if literal > 0 then
    mkApp (mkConst ``R5NamedLiteral.pos) name
  else
    mkApp (mkConst ``R5NamedLiteral.neg) name

def unitListExpr (names : Array Expr)
    (descriptors : Array VariableDescriptor)
    (clauses supportClauses : Array (Array Int)) : MetaM Expr := do
  let mut units := #[]
  let mut literals : Array Int := #[]
  for source in #[clauses, supportClauses] do
    for clause in source do
      if clause.size = 1 then
        let literal := clause[0]!
        let variableIndex := literal.natAbs
        if variableIndex = 0 ∨ descriptors.size < variableIndex then
          throwError m!"unit variable outside allocation: {literal}"
        match descriptors[variableIndex - 1]! with
        | .edge _ _ =>
            unless literals.contains literal do
              literals := literals.push literal
        | _ => pure ()
  for literal in literals do
    units := units.push (← namedLiteralExpr names literal)
  return listExpr (mkConst ``R5NamedLiteral) units

def signedUnitDescriptors (descriptors : Array VariableDescriptor)
    (clauses supportClauses : Array (Array Int)) :
    Except String (List SignedVariable) := do
  let mut result := []
  for source in #[clauses, supportClauses] do
    for clause in source do
      if clause.size = 1 then
        let described ← describeClause descriptors clause
        match described with
        | [literal] =>
            if !result.contains literal then
              result := literal :: result
        | _ => pure ()
  return result.reverse

def membershipProof (element container : Expr) : MetaM Expr := do
  let proposition ← Meta.mkAppM ``Membership.mem #[container, element]
  Meta.mkDecideProof proposition

def fieldProof (field : Name) (assumptions : Expr) : MetaM Expr :=
  Meta.mkAppM field #[assumptions]

def validateProofType (graph clause proof : Expr) : MetaM Expr := do
  let expected ← Meta.mkAppM ``R5NamedClause.Valid #[graph, clause]
  let actual ← Meta.inferType proof
  unless ← Meta.isDefEq actual expected do
    throwError m!"semantic proof has wrong clause type\nexpected: {expected}\nactual: {actual}"
  return proof

def degreeProof? (graph assumptions : Expr)
    (described : List SignedVariable) : MetaM (Option Expr) := do
  let hregular ← fieldProof ``R5CoreAssumptions.regular assumptions
  match described with
  | [{ positive := true,
       descriptor := .degreeCounter vertex 25 5 }] =>
      let v ← finExpr 26 vertex
      return some (← Meta.mkAppM ``r5DegreeClause_terminal_five
        #[graph, hregular, v])
  | [{ positive := false,
       descriptor := .degreeCounter vertex 25 6 }] =>
      let v ← finExpr 26 vertex
      return some (← Meta.mkAppM ``r5DegreeClause_terminal_six
        #[graph, hregular, v])
  | [{ positive := false,
       descriptor := .degreeCounter vertex firstPrefix firstThreshold },
     { positive := true,
       descriptor := .degreeCounter vertex' secondPrefix secondThreshold }] =>
      if vertex = vertex' ∧ secondPrefix = firstPrefix + 1 ∧
          firstThreshold = secondThreshold then
        let v ← finExpr 26 vertex
        return some (← Meta.mkAppM ``r5DegreeClause_previous_current
          #[graph, v, natLit firstPrefix, natLit firstThreshold])
      else if vertex = vertex' ∧ firstPrefix = secondPrefix + 1 ∧
          firstThreshold = firstPrefix ∧
          secondThreshold = secondPrefix then
        let v ← finExpr 26 vertex
        let p ← finExpr 25 secondPrefix
        return some (← Meta.mkAppM ``r5DegreeClause_diagonal_previous
          #[graph, v, p])
      else
        return none
  | [{ positive := false,
       descriptor := .degreeCounter vertex currentPrefix currentThreshold },
     { positive := true,
       descriptor := .degreeCounter vertex' previousPrefix previousThreshold },
     { positive := true, descriptor := .edge edgeLeft edgeRight }] =>
      if vertex = vertex' ∧ currentPrefix = previousPrefix + 1 ∧
          currentThreshold = 1 ∧ previousThreshold = 1 ∧
          .edge edgeLeft edgeRight = incidentEdge vertex previousPrefix then
        let v ← finExpr 26 vertex
        let p ← finExpr 25 previousPrefix
        return some (← Meta.mkAppM ``r5DegreeClause_current_one_elim
          #[graph, v, p])
      else if vertex = vertex' ∧ currentPrefix = previousPrefix + 1 ∧
          currentThreshold = previousThreshold ∧
          0 < currentThreshold ∧
          .edge edgeLeft edgeRight = incidentEdge vertex previousPrefix then
        let v ← finExpr 26 vertex
        let p ← finExpr 25 previousPrefix
        return some (← Meta.mkAppM ``r5DegreeClause_current_elim_input
          #[graph, v, p, natLit (currentThreshold - 1)])
      else
        return none
  | [{ positive := false, descriptor := .edge edgeLeft edgeRight },
     { positive := true,
       descriptor := .degreeCounter vertex currentPrefix 1 }] =>
      if 0 < currentPrefix ∧
          .edge edgeLeft edgeRight =
            incidentEdge vertex (currentPrefix - 1) then
        let v ← finExpr 26 vertex
        let p ← finExpr 25 (currentPrefix - 1)
        return some (← Meta.mkAppM ``r5DegreeClause_input_current_one
          #[graph, v, p])
      else
        return none
  | [{ positive := false,
       descriptor := .degreeCounter vertex currentPrefix currentThreshold },
     { positive := true,
       descriptor := .degreeCounter vertex' previousPrefix sameThreshold },
     { positive := true,
       descriptor := .degreeCounter vertex'' previousPrefix'
         lowerThreshold }] =>
      if vertex = vertex' ∧ vertex = vertex'' ∧
          currentPrefix = previousPrefix + 1 ∧
          previousPrefix = previousPrefix' ∧
          currentThreshold = sameThreshold ∧
          currentThreshold = lowerThreshold + 1 then
        let v ← finExpr 26 vertex
        let p ← finExpr 25 previousPrefix
        return some (← Meta.mkAppM ``r5DegreeClause_current_elim_previous
          #[graph, v, p, natLit lowerThreshold])
      else
        return none
  | [{ positive := false,
       descriptor := .degreeCounter vertex previousPrefix lowerThreshold },
     { positive := false, descriptor := .edge edgeLeft edgeRight },
     { positive := true,
       descriptor := .degreeCounter vertex' currentPrefix currentThreshold }] =>
      if vertex = vertex' ∧ currentPrefix = previousPrefix + 1 ∧
          currentThreshold = lowerThreshold + 1 ∧
          .edge edgeLeft edgeRight = incidentEdge vertex previousPrefix then
        let v ← finExpr 26 vertex
        let p ← finExpr 25 previousPrefix
        return some (← Meta.mkAppM ``r5DegreeClause_previous_input_current
          #[graph, v, p, natLit lowerThreshold])
      else
        return none
  | [{ positive := false,
       descriptor := .degreeCounter vertex currentPrefix currentThreshold },
     { positive := true, descriptor := .edge edgeLeft edgeRight }] =>
      if 0 < currentPrefix ∧ currentThreshold = currentPrefix ∧
          .edge edgeLeft edgeRight =
            incidentEdge vertex (currentPrefix - 1) then
        let v ← finExpr 26 vertex
        let p ← finExpr 25 (currentPrefix - 1)
        return some (← Meta.mkAppM ``r5DegreeClause_diagonal_input
          #[graph, v, p])
      else
        return none
  | _ => return none

def natUnorderedPairs : List Nat → List (Nat × Nat)
  | [] => []
  | head :: tail =>
      tail.map (fun right => (head, right)) ++ natUnorderedPairs tail

def sixSetVertices? (positive : Bool)
    (described : List SignedVariable) : Option (List Nat) := do
  if described.length != 15 then failure
  let edges ← described.mapM fun literal => do
    if literal.positive != positive then failure
    match literal.descriptor with
    | .edge left right => pure (left, right)
    | _ => failure
  let vertices :=
    (List.range 26).filter fun vertex =>
      edges.any fun edge => edge.1 == vertex || edge.2 == vertex
  if vertices.length != 6 then failure
  let expected := natUnorderedPairs vertices
  if edges != expected then failure
  return vertices

def sixSetProof? (graph assumptions : Expr)
    (described : List SignedVariable) : MetaM (Option Expr) := do
  let hClique ← fieldProof ``R5CoreAssumptions.cliqueFree assumptions
  let hIndep ← fieldProof ``R5CoreAssumptions.indepSetFree assumptions
  match sixSetVertices? true described with
  | some vertices =>
      let list ← finListExpr vertices
      let lengthExpr ← Meta.mkAppM ``List.length #[list]
      let cardProp ← Meta.mkEq lengthExpr (natLit 6)
      let hcard ← Meta.mkDecideProof cardProp
      let nodupProp ← Meta.mkAppM ``List.Nodup #[list]
      let hnodup ← Meta.mkDecideProof nodupProp
      return some (← Meta.mkAppM ``r5PositivePairClause_valid
        #[graph, hIndep, list, hcard, hnodup])
  | none =>
      match sixSetVertices? false described with
      | some vertices =>
          let list ← finListExpr vertices
          let lengthExpr ← Meta.mkAppM ``List.length #[list]
          let cardProp ← Meta.mkEq lengthExpr (natLit 6)
          let hcard ← Meta.mkDecideProof cardProp
          let nodupProp ← Meta.mkAppM ``List.Nodup #[list]
          let hnodup ← Meta.mkDecideProof nodupProp
          return some (← Meta.mkAppM ``r5NegativePairClause_valid
            #[graph, hClique, list, hcard, hnodup])
      | none => return none

def exteriorEdge (vertex position : Nat) : VariableDescriptor :=
  .edge (position + 1) vertex

def sortedComparisonProof (scheme : R5Reify.ComparisonScheme)
    (assumptions : Expr) (left right : Nat) : MetaM Expr := do
  let hsorted ← fieldProof ``R5CoreAssumptions.sorted assumptions
  let pair := natPairExpr left right
  let comparisons := comparisonListExpr scheme
  let hmem ← membershipProof pair comparisons
  return mkApp2 hsorted pair hmem

def lexProof? (scheme : R5Reify.ComparisonScheme)
    (graph assumptions : Expr)
    (described : List SignedVariable) : MetaM (Option Expr) := do
  let bounds (left right position : Nat) := do
    let hl ← natLtProof left 26
    let hlext ← natLeProof 6 left
    let hr ← natLtProof right 26
    let hrext ← natLeProof 6 right
    let hp ← natLtProof position 5
    return (hl, hlext, hr, hrext, hp)
  match described with
  | [{ positive := false, descriptor := .edge 1 left },
     { positive := true, descriptor := .edge 1 right }] =>
      let (hl, hlext, hr, hrext, _) ← bounds left right 0
      let hlex ← sortedComparisonProof scheme assumptions left right
      return some (← Meta.mkAppM ``r5LexClause_zero_order
        #[graph, natLit left, natLit right,
          hl, hlext, hr, hrext, hlex])
  | [{ positive := false,
       descriptor := .lexPrefix left right prefixPosition },
     { positive := false, descriptor := leftEdge },
     { positive := true, descriptor := rightEdge }] =>
      if leftEdge = exteriorEdge left (prefixPosition + 1) ∧
          rightEdge = exteriorEdge right (prefixPosition + 1) then
        let position := prefixPosition + 1
        let (hl, hlext, hr, hrext, hp) ← bounds left right position
        let hpositive ← natLtProof 0 position
        let hlex ← sortedComparisonProof scheme assumptions left right
        return some (← Meta.mkAppM ``r5LexClause_succ_order
          #[graph, natLit left, natLit right, natLit position,
            hl, hlext, hr, hrext, hpositive, hp, hlex])
      else if leftEdge = exteriorEdge left prefixPosition ∧
          rightEdge = exteriorEdge right prefixPosition then
        let (hl, hlext, hr, hrext, hp) ←
          bounds left right prefixPosition
        return some (← Meta.mkAppM ``r5LexClause_current_forward
          #[graph, natLit left, natLit right, natLit prefixPosition,
            hl, hlext, hr, hrext, hp])
      else
        return none
  | [{ positive := false,
       descriptor := .lexPrefix left right position },
     { positive := true,
       descriptor := .lexPrefix left' right' previousPosition }] =>
      if left = left' ∧ right = right' ∧ 0 < position ∧
          previousPosition + 1 = position then
        let hpositive ← natLtProof 0 position
        return some (← Meta.mkAppM ``r5LexClause_current_previous
          #[graph, natLit left, natLit right, natLit position, hpositive])
      else
        return none
  | [{ positive := false,
       descriptor := .lexPrefix left right position },
     { positive := true, descriptor := leftEdge },
     { positive := false, descriptor := rightEdge }] =>
      if leftEdge = exteriorEdge left position ∧
          rightEdge = exteriorEdge right position then
        let (hl, hlext, hr, hrext, hp) ← bounds left right position
        return some (← Meta.mkAppM ``r5LexClause_current_reverse
          #[graph, natLit left, natLit right, natLit position,
            hl, hlext, hr, hrext, hp])
      else
        return none
  | [{ positive := false, descriptor := leftEdge },
     { positive := false, descriptor := rightEdge },
     { positive := true, descriptor := .lexPrefix left right 0 }] =>
      if leftEdge = exteriorEdge left 0 ∧
          rightEdge = exteriorEdge right 0 then
        let (hl, hlext, hr, hrext, _) ← bounds left right 0
        return some (← Meta.mkAppM ``r5LexClause_zero_both_true
          #[graph, natLit left, natLit right, hl, hlext, hr, hrext])
      else
        return none
  | [{ positive := true, descriptor := leftEdge },
     { positive := true, descriptor := rightEdge },
     { positive := true, descriptor := .lexPrefix left right 0 }] =>
      if leftEdge = exteriorEdge left 0 ∧
          rightEdge = exteriorEdge right 0 then
        let (hl, hlext, hr, hrext, _) ← bounds left right 0
        return some (← Meta.mkAppM ``r5LexClause_zero_both_false
          #[graph, natLit left, natLit right, hl, hlext, hr, hrext])
      else
        return none
  | [{ positive := false,
       descriptor := .lexPrefix left right previousPosition },
     { positive := false, descriptor := leftEdge },
     { positive := false, descriptor := rightEdge },
     { positive := true,
       descriptor := .lexPrefix left' right' position }] =>
      if left = left' ∧ right = right' ∧
          position = previousPosition + 1 ∧
          leftEdge = exteriorEdge left position ∧
          rightEdge = exteriorEdge right position then
        let (hl, hlext, hr, hrext, hp) ← bounds left right position
        let hpositive ← natLtProof 0 position
        return some (← Meta.mkAppM ``r5LexClause_succ_both_true
          #[graph, natLit left, natLit right, natLit position,
            hl, hlext, hr, hrext, hpositive, hp])
      else
        return none
  | [{ positive := false,
       descriptor := .lexPrefix left right previousPosition },
     { positive := true, descriptor := leftEdge },
     { positive := true, descriptor := rightEdge },
     { positive := true,
       descriptor := .lexPrefix left' right' position }] =>
      if left = left' ∧ right = right' ∧
          position = previousPosition + 1 ∧
          leftEdge = exteriorEdge left position ∧
          rightEdge = exteriorEdge right position then
        let (hl, hlext, hr, hrext, hp) ← bounds left right position
        let hpositive ← natLtProof 0 position
        return some (← Meta.mkAppM ``r5LexClause_succ_both_false
          #[graph, natLit left, natLit right, natLit position,
            hl, hlext, hr, hrext, hpositive, hp])
      else
        return none
  | _ => return none

def positiveUnitEdges (units : List SignedVariable) :
    List (Nat × Nat) :=
  (List.range 26).flatMap fun left =>
    (List.range (25 - left)).filterMap fun offset =>
      let right := left + offset + 1
      if units.contains {
          positive := true
          descriptor := .edge left right
        } then
        some (left, right)
      else
        none

def admissibilityWitness?
    (units described : List SignedVariable) :
    Option (List Nat × List (Nat × Nat) × List (Nat × Nat)) := do
  if described.length != 6 && described.length != 7 then failure
  let variablePairs ← described.mapM fun literal => do
    if literal.positive then failure
    match literal.descriptor with
    | .edge left right => pure (left, right)
    | _ => failure
  let endpoints :=
    (List.range 26).filter fun vertex =>
      variablePairs.any fun pair =>
        pair.1 == vertex || pair.2 == vertex
  if 6 < endpoints.length then failure
  let missing := 6 - endpoints.length
  let available :=
    (List.range 26).filter fun vertex => !endpoints.contains vertex
  let positivePairs := positiveUnitEdges units
  for added in available.sublistsLen missing do
    let vertices :=
      (List.range 26).filter fun vertex =>
        endpoints.contains vertex || added.contains vertex
    let fixedCandidates := positivePairs.filter fun pair =>
      vertices.contains pair.1 && vertices.contains pair.2 &&
        !variablePairs.contains pair
    let needed := 12 - variablePairs.length
    if needed ≤ fixedCandidates.length then
      return (vertices, fixedCandidates.take needed, variablePairs)
  failure

def finsetExpr (vertices : List Nat) : MetaM Expr := do
  let list ← finListExpr vertices
  Meta.mkAppM ``List.toFinset #[list]

def inducedPairListExpr (vertices : Expr)
    (pairs : List (Nat × Nat)) : MetaM Expr := do
  let subtypeType ← Meta.mkAppM ``R5VertexIn #[vertices]
  let pairType := mkApp2 (mkConst ``Prod [.zero, .zero])
    subtypeType subtypeType
  let mut pairExprs := Array.mkEmpty pairs.length
  for pair in pairs do
    let left ← finExpr 26 pair.1
    let right ← finExpr 26 pair.2
    let hleft ← membershipProof left vertices
    let hright ← membershipProof right vertices
    let leftSubtype ← Meta.mkAppM ``Subtype.mk #[left, hleft]
    let rightSubtype ← Meta.mkAppM ``Subtype.mk #[right, hright]
    let pairExpr ← Meta.mkAppM ``Prod.mk #[leftSubtype, rightSubtype]
    pairExprs := pairExprs.push pairExpr
  return listExpr pairType pairExprs

def equalityDecideProof (left right : Expr) : MetaM Expr := do
  let proposition ← Meta.mkEq left right
  Meta.mkDecideProof proposition

def admissibilityProof? (graph assumptions units : Expr)
    (unitDescriptors described : List SignedVariable) :
    MetaM (Option Expr) := do
  let some (vertexValues, fixedValues, variableValues) :=
      admissibilityWitness? unitDescriptors described
    | return none
  let vertices ← finsetExpr vertexValues
  let fixedPairs ← inducedPairListExpr vertices fixedValues
  let variablePairs ← inducedPairListExpr vertices variableValues
  let combinedPairs ← Meta.mkAppM ``List.append #[fixedPairs, variablePairs]
  let vertexCard ← Meta.mkAppM ``Finset.card #[vertices]
  let hvertexCard ← equalityDecideProof vertexCard (natLit 6)
  let loopless ← Meta.mkAppM ``r5InducedPairsLoopless
    #[vertices, combinedPairs]
  let hloopless ← Meta.mkDecideProof loopless
  let witness ← Meta.mkAppM ``r5InducedPairEdgeFinset
    #[vertices, combinedPairs]
  let witnessCard ← Meta.mkAppM ``Finset.card #[witness]
  let hwitnessCard ← equalityDecideProof witnessCard (natLit 12)
  let fixedCovered ← Meta.mkAppM ``r5FixedPairsCoveredByUnits
    #[vertices, fixedPairs, units]
  let hfixedCovered ← Meta.mkDecideProof fixedCovered
  let hAdmissible ←
    fieldProof ``R5CoreAssumptions.admissible assumptions
  let hUnits ← fieldProof ``R5CoreAssumptions.unitsTrue assumptions
  return some (← Meta.mkAppM
    ``r5NegativeInducedPairClause_valid_of_admissible
    #[graph, hAdmissible, vertices, fixedPairs, variablePairs,
      hvertexCard, hloopless, hwitnessCard, units, hUnits,
      hfixedCovered])

def unitProof (graph assumptions units literal : Expr) : MetaM Expr := do
  let hunits ← fieldProof ``R5CoreAssumptions.unitsTrue assumptions
  let hmem ← membershipProof literal units
  let htrue := mkApp2 hunits literal hmem
  Meta.mkAppM ``R5NamedClause.valid_singleton #[graph, literal, htrue]

def validClauseProof (scheme : R5Reify.ComparisonScheme)
    (graph assumptions units : Expr)
    (unitDescriptors : List SignedVariable)
    (names : Array Expr) (descriptors : Array VariableDescriptor)
    (clause : Array Int) : MetaM Expr := do
  let clauseExpr ← R5Reify.namedLiteralListExpr names clause
  let described ←
    match describeClause descriptors clause with
    | .ok value => pure value
    | .error error => throwError error
  if let some proof ← degreeProof? graph assumptions described then
    return ← validateProofType graph clauseExpr proof
  if let some proof ← sixSetProof? graph assumptions described then
    return ← validateProofType graph clauseExpr proof
  if let some proof ← lexProof? scheme graph assumptions described then
    return ← validateProofType graph clauseExpr proof
  if let some proof ←
      admissibilityProof? graph assumptions units unitDescriptors described then
    return ← validateProofType graph clauseExpr proof
  if clause.size = 1 then
    let literal ← namedLiteralExpr names clause[0]!
    let proof ← unitProof graph assumptions units literal
    return ← validateProofType graph clauseExpr proof
  throwError m!"unclassified retained core clause: {repr described}"

partial def eliminateFalsified
    (scheme : R5Reify.ComparisonScheme)
    (graph adjacencyInstance assumptions units : Expr)
    (unitDescriptors : List SignedVariable)
    (names : Array Expr) (descriptors : Array VariableDescriptor)
    (clauses : Array (Array Int)) (source : Expr)
    (start stop : Nat) : MetaM Expr := do
  match stop - start with
  | 0 => throwError "cannot eliminate an empty core"
  | 1 =>
      let valid ← validClauseProof scheme graph assumptions units
        unitDescriptors
        names descriptors clauses[start]!
      let notFalsified ←
        Meta.mkAppM ``R5NamedClause.not_falsified_of_valid #[graph, valid]
      return mkApp notFalsified source
  | length =>
      let middle := start + length / 2
      let leftType ← R5Reify.buildNamedFalsification
        graph adjacencyInstance
        names clauses start middle
      let rightType ← R5Reify.buildNamedFalsification
        graph adjacencyInstance
        names clauses middle stop
      Meta.withLocalDecl `left .default leftType fun left => do
        let leftFalse ← eliminateFalsified scheme graph adjacencyInstance
          assumptions units unitDescriptors
          names descriptors clauses left start middle
        let leftFunction ← Meta.mkLambdaFVars #[left] leftFalse
        Meta.withLocalDecl `right .default rightType fun right => do
          let rightFalse ← eliminateFalsified scheme graph adjacencyInstance
            assumptions units unitDescriptors
            names descriptors clauses right middle stop
          let rightFunction ← Meta.mkLambdaFVars #[right] rightFalse
          Meta.mkAppM ``Or.elim #[source, leftFunction, rightFunction]

def closeCore (outputName theoremName : Name)
    (scheme : R5Reify.ComparisonScheme) (variableCount : Nat)
    (clauses supportClauses : Array (Array Int)) : MetaM Unit := do
  let names := R5Reify.variableNameExprs scheme
  let descriptors := variableDescriptors scheme
  unless variableCount == names.size && names.size == descriptors.size do
    let nameCount := names.size
    let descriptorCount := descriptors.size
    throwError
      m!"core header/allocation mismatch: {variableCount}, {nameCount}, {descriptorCount}"
  let units ← unitListExpr names descriptors clauses supportClauses
  let unitDescriptors ←
    match signedUnitDescriptors descriptors clauses supportClauses with
    | .ok value => pure value
    | .error error => throwError error
  let comparisons := comparisonListExpr scheme
  let fin26 := mkApp (mkConst ``Fin) (natLit 26)
  let graphType := mkApp (mkConst ``SimpleGraph [.zero]) fin26
  Meta.withLocalDecl `G .default graphType fun graph => do
    let adjacency :=
      mkApp2 (mkConst ``SimpleGraph.Adj [.zero]) fin26 graph
    let instanceType :=
      mkApp3
        (mkConst ``DecidableRel [.succ .zero, .succ .zero])
        fin26 fin26 adjacency
    Meta.withLocalDecl `inst .instImplicit instanceType fun adjacencyInstance => do
      let assumptionType ← Meta.mkAppM ``R5CoreAssumptions
        #[graph, comparisons, units]
      Meta.withLocalDecl `h .default assumptionType fun assumptions => do
        let source := mkApp2 (mkConst theoremName) graph adjacencyInstance
        let sourceType ← Meta.inferType source
        let expectedType ← R5Reify.buildNamedFalsification
          graph adjacencyInstance names clauses 0 clauses.size
        unless ← Meta.isDefEq sourceType expectedType do
          throwError "named reified theorem does not match the parsed core"
        let contradiction ← eliminateFalsified scheme graph adjacencyInstance
          assumptions units unitDescriptors
          names descriptors clauses source 0 clauses.size
        let value ← Meta.mkLambdaFVars
          #[graph, adjacencyInstance, assumptions] contradiction
        let type ← Meta.mkForallFVars
          #[graph, adjacencyInstance, assumptions] (mkConst ``False)
        addDecl <| Declaration.thmDecl {
          name := outputName
          levelParams := []
          type
          value
        }

end Erdos617.R5CoreSemantics

syntax (name := r5CloseReifiedCore)
  "r5_close_reified_core " ident ppSpace
    ("full_exterior" <|> "zero_anchor") ppSpace ident ppSpace str : command

syntax (name := r5CloseReifiedCoreWithUnits)
  "r5_close_reified_core_with_units " ident ppSpace
    ("full_exterior" <|> "zero_anchor") ppSpace ident ppSpace
    str ppSpace str : command

elab_rules : command
  | `(r5_close_reified_core $output:ident full_exterior
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
            Erdos617.R5CoreSemantics.closeCore outputName theoremName
              .fullExterior variableCount clauses clauses
  | `(r5_close_reified_core $output:ident zero_anchor
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
            Erdos617.R5CoreSemantics.closeCore outputName theoremName
              .zeroAnchor variableCount clauses clauses
  | `(r5_close_reified_core_with_units $output:ident full_exterior
      $source:ident $corePath:str $unitsPath:str) => do
      let theoremName ← resolveGlobalConstNoOverload source
      let outputName := (← getCurrNamespace) ++ output.getId
      let coreData ← IO.FS.readFile corePath.getString
      let unitDataRaw ← IO.FS.readFile unitsPath.getString
      let unitData :=
        Erdos617.R5CoreSemantics.stripDimacsComments unitDataRaw
      match Mathlib.Tactic.Sat.Parser.parseDimacs
          ⟨coreData, coreData.startPos⟩,
        Mathlib.Tactic.Sat.Parser.parseDimacs
          ⟨unitData, unitData.startPos⟩ with
      | Std.Internal.Parsec.ParseResult.success coreNext
          (variableCount, clauses),
        Std.Internal.Parsec.ParseResult.success unitNext
          (unitVariableCount, unitClauses) =>
          unless coreNext.2.IsAtEnd && unitNext.2.IsAtEnd do
            throwError "trailing core or unit CNF input"
          unless variableCount = unitVariableCount do
            throwError "core and unit CNFs have different variable counts"
          Command.liftTermElabM do
            Erdos617.R5CoreSemantics.closeCore outputName theoremName
              .fullExterior variableCount clauses unitClauses
      | Std.Internal.Parsec.ParseResult.error _ error, _ =>
          throwError m!"parse core CNF failed: {error}"
      | _, Std.Internal.Parsec.ParseResult.error _ error =>
          throwError m!"parse unit CNF failed: {error}"
  | `(r5_close_reified_core_with_units $output:ident zero_anchor
      $source:ident $corePath:str $unitsPath:str) => do
      let theoremName ← resolveGlobalConstNoOverload source
      let outputName := (← getCurrNamespace) ++ output.getId
      let coreData ← IO.FS.readFile corePath.getString
      let unitDataRaw ← IO.FS.readFile unitsPath.getString
      let unitData :=
        Erdos617.R5CoreSemantics.stripDimacsComments unitDataRaw
      match Mathlib.Tactic.Sat.Parser.parseDimacs
          ⟨coreData, coreData.startPos⟩,
        Mathlib.Tactic.Sat.Parser.parseDimacs
          ⟨unitData, unitData.startPos⟩ with
      | Std.Internal.Parsec.ParseResult.success coreNext
          (variableCount, clauses),
        Std.Internal.Parsec.ParseResult.success unitNext
          (unitVariableCount, unitClauses) =>
          unless coreNext.2.IsAtEnd && unitNext.2.IsAtEnd do
            throwError "trailing core or unit CNF input"
          unless variableCount = unitVariableCount do
            throwError "core and unit CNFs have different variable counts"
          Command.liftTermElabM do
            Erdos617.R5CoreSemantics.closeCore outputName theoremName
              .zeroAnchor variableCount clauses unitClauses
      | Std.Internal.Parsec.ParseResult.error _ error, _ =>
          throwError m!"parse core CNF failed: {error}"
      | _, Std.Internal.Parsec.ParseResult.error _ error =>
          throwError m!"parse unit CNF failed: {error}"

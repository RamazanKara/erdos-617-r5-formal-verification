import Erdos617.Sat.SpecialBrooksE043P19Bridge
import E058SemanticE043Parent19Child00Closure
import E058SemanticE043Parent19Child01Closure
import E058SemanticE043Parent19Child02Closure
import E058SemanticE043Parent19Child03Closure
import E058SemanticE043Parent19Child04Closure

open Finset Fintype

namespace Erdos617

set_option maxHeartbeats 400000 in
-- Five finite unit-list inclusions are discharged after splitting `child`.
set_option maxRecDepth 10000 in
theorem e058E043P19Contradiction
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (child : Fin 5)
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hG : Admissible G)
    (hclique : G.CliqueFree 6)
    (hindep : G.IndepSetFree 6)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (hsorted : R5ComparisonsSorted G r5FullExteriorComparisons)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
        left right)
    (hcodes : ∀ row : Fin 20,
      r5ExteriorPatternCode G ((row : Nat) + 6) =
        r5CrossPatternSortedCode 19 row)
    (hanchor : ∀ offset : Fin 19,
      decide (G.Adj 6
        ⟨(offset : Nat) + 7, by omega⟩) =
      r5P19AnchorTargetBit child offset) :
    False := by
  have hcanonical :=
    r5CanonicalE043P19Units_allTrue
      G child hneighbor horbit hcodes hanchor
  fin_cases child
  · apply E058SemanticE043Parent19Child00Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent19Child01Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent19Child02Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent19Child03Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent19Child04Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide

set_option maxHeartbeats 400000 in
-- The canonical bridge composes two finite permutations.
set_option maxRecDepth 10000 in
theorem e058E043P19CanonicalContradiction
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hG : Admissible G)
    (hclique : G.CliqueFree 6)
    (hindep : G.IndepSetFree 6)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode 19))
        left right)
    (hcodes : ∀ row : Fin 20,
      r5ExteriorPatternCode G ((row : Nat) + 6) =
        r5CrossPatternSortedCode 19 row) :
    False := by
  obtain ⟨child, relabeling, hregular', hG', hclique',
      hindep', hneighbor', hsorted', horbit', hcodes',
      hanchor'⟩ :=
    exists_r5CanonicalE043P19Child
      G hregular hG hclique hindep hneighbor horbit hcodes
  exact e058E043P19Contradiction
    (relabelGraph G relabeling) child
    hregular' hG' hclique' hindep'
    hneighbor' hsorted' horbit' hcodes' hanchor'

#print axioms e058E043P19CanonicalContradiction
#check e058E043P19CanonicalContradiction

end Erdos617

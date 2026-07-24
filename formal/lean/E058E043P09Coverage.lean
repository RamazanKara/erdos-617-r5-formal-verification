import Erdos617.Sat.SpecialBrooksE043P09Bridge
import E058SemanticE043Parent09Child00Closure
import E058SemanticE043Parent09Child01Closure
import E058SemanticE043Parent09Child02Closure
import E058SemanticE043Parent09Child03Closure
import E058SemanticE043Parent09Child04Closure
import E058SemanticE043Parent09Child05Closure
import E058SemanticE043Parent09Child06Closure
import E058SemanticE043Parent09Child07Closure
import E058SemanticE043Parent09Child08Closure
import E058SemanticE043Parent09Child09Closure
import E058SemanticE043Parent09Child10Closure
import E058SemanticE043Parent09Child11Closure
import E058SemanticE043Parent09Child12Closure
import E058SemanticE043Parent09Child13Closure
import E058SemanticE043Parent09Child14Closure
import E058SemanticE043Parent09Child15Closure

open Finset Fintype

namespace Erdos617

set_option maxHeartbeats 800000 in
-- Sixteen finite unit-list inclusions are discharged after splitting `child`.
set_option maxRecDepth 10000 in
theorem e058E043P09Contradiction
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (child : Fin 16)
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
        r5CrossPatternSortedCode 9 row)
    (hanchor : ∀ offset : Fin 19,
      decide (G.Adj 6
        ⟨(offset : Nat) + 7, by omega⟩) =
      r5P09AnchorTargetBit child offset) :
    False := by
  have hcanonical :=
    r5CanonicalE043P09Units_allTrue
      G child hneighbor horbit hcodes hanchor
  fin_cases child
  · apply E058SemanticE043Parent09Child00Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child01Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child02Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child03Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child04Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child05Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child06Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child07Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child08Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child09Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child10Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child11Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child12Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child13Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child14Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent09Child15Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide

set_option maxHeartbeats 800000 in
-- The canonical bridge composes two finite permutations.
set_option maxRecDepth 10000 in
theorem e058E043P09CanonicalContradiction
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
        r5CrossPatternSortedCode 9 row) :
    False := by
  obtain ⟨child, relabeling, hregular', hG', hclique',
      hindep', hneighbor', hsorted', horbit', hcodes',
      hanchor'⟩ :=
    exists_r5CanonicalE043P09Child
      G hregular hG hclique hindep hneighbor horbit hcodes
  exact e058E043P09Contradiction
    (relabelGraph G relabeling) child
    hregular' hG' hclique' hindep'
    hneighbor' hsorted' horbit' hcodes' hanchor'

#print axioms e058E043P09CanonicalContradiction
#check e058E043P09CanonicalContradiction

end Erdos617

import Erdos617.Sat.SpecialBrooksBranch19Bridge
import E058SemanticE042Child00Closure
import E058SemanticE042Child01Closure
import E058SemanticE042Child02Closure
import E058SemanticE042Child03Closure
import E058SemanticE042Child05Closure
import E058SemanticE042Child06Closure
import E058SemanticE042Child07Closure
import E058SemanticE042Child08Closure
import E058SemanticE042Child10Closure
import E058SemanticE042Child11Closure
import E058SemanticE042Child12Closure
import E058SemanticE042Child13Closure
import E058SemanticE042Child14Closure
import E058SemanticE042Child15Closure
import E058SemanticE042Child16Closure
import E058SemanticE042Child17Closure
import E058SemanticE042Child18Closure

open Finset Fintype

namespace Erdos617

set_option maxHeartbeats 800000 in
-- Seventeen finite unit-list inclusions are discharged after splitting `child`.
set_option maxRecDepth 10000 in
theorem e058E042DirectContradiction
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (child : Fin 20)
    (hnot04 : child ≠ 4)
    (hnot09 : child ≠ 9)
    (hnot19 : child ≠ 19)
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
        r5CrossPatternSortedCode child row) :
    False := by
  have hcanonical :=
    r5CanonicalE042Units_allTrue
      G child hneighbor horbit hcodes
  fin_cases child
  · apply E058SemanticE042Child00Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE042Child01Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE042Child02Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE042Child03Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · exact (hnot04 rfl).elim
  · apply E058SemanticE042Child05Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE042Child06Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE042Child07Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE042Child08Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · exact (hnot09 rfl).elim
  · apply E058SemanticE042Child10Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE042Child11Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE042Child12Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE042Child13Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE042Child14Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE042Child15Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE042Child16Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE042Child17Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE042Child18Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · exact (hnot19 rfl).elim

#print axioms e058E042DirectContradiction
#check e058E042DirectContradiction

end Erdos617

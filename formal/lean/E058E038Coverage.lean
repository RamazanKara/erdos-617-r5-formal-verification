import Erdos617.Sat.SpecialBrooksBranchUnits
import E058SemanticE038Branch00Closure
import E058SemanticE038Branch01Closure
import E058SemanticE038Branch02Closure
import E058SemanticE038Branch03Closure
import E058SemanticE038Branch04Closure
import E058SemanticE038Branch05Closure
import E058SemanticE038Branch06Closure
import E058SemanticE038Branch07Closure
import E058SemanticE038Branch08Closure
import E058SemanticE038Branch09Closure
import E058SemanticE038Branch10Closure
import E058SemanticE038Branch11Closure
import E058SemanticE038Branch12Closure
import E058SemanticE038Branch13Closure
import E058SemanticE038Branch14Closure
import E058SemanticE038Branch15Closure
import E058SemanticE038Branch16Closure
import E058SemanticE038Branch17Closure
import E058SemanticE038Branch18Closure

open Finset Fintype

namespace Erdos617

set_option maxHeartbeats 0 in
theorem e058E038Contradiction
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (branch : Fin 26) (hbranch : branch < 19)
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hG : Admissible G)
    (hclique : G.CliqueFree 6)
    (hindep : G.IndepSetFree 6)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (hsorted : R5ComparisonsSorted G r5FullExteriorComparisons)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left) (r5NeighborVertex right)) =
        r5FiveVertexAdjacency
          (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
          left right) :
    False := by
  have hcanonical :=
    r5CanonicalBranchUnits_allTrue
      G branch hneighbor horbit
  fin_cases branch
  · apply E058SemanticE038Branch00Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch01Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch02Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch03Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch04Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch05Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch06Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch07Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch08Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch09Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch10Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch11Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch12Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch13Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch14Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch15Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch16Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch17Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE038Branch18Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  all_goals
    revert hbranch
    decide

#print axioms e058E038Contradiction
#check e058E038Contradiction

end Erdos617

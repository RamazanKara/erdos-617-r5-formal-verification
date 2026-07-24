import E058E038Coverage
import E058E042Coverage
import E058E045Coverage
import Erdos617.ResidualDegreeFive

open Finset Fintype

namespace Erdos617

/-- Every one of the 26 canonical neighborhood branches is impossible. -/
theorem e058SpecialBrooksBranchContradiction
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (branch : Fin 26)
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
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
        left right) :
    False := by
  by_cases hlt : branch < 19
  · exact e058E038Contradiction
      G branch hlt hregular hG hclique hindep
      hneighbor hsorted horbit
  by_cases heq : branch = 19
  · subst branch
    exact e058E042CanonicalContradiction
      G hregular hG hclique hindep hneighbor horbit
  have hge : 20 ≤ branch := by omega
  exact e058E045CanonicalContradiction
    G branch hge hregular hG hclique hindep
    hneighbor horbit

/-- The special-Brooks graph is impossible once the neighborhood of vertex
zero has been normalized. -/
theorem e058NormalizedSpecialBrooksContradiction
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hG : Admissible G)
    (hclique : G.CliqueFree 6)
    (hindep : G.IndepSetFree 6)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors) :
    False := by
  obtain ⟨branch, relabeling, hregular', hG', hclique',
      hindep', hneighbor', hsorted', horbit'⟩ :=
    exists_r5CanonicalSpecialBrooksBranch_of_normalized
      G hregular hG hclique hindep hneighbor
  exact e058SpecialBrooksBranchContradiction
    (relabelGraph G relabeling) branch
    hregular' hG' hclique' hindep'
    hneighbor' hsorted' horbit'

/-- Unrestricted finite special-Brooks obstruction certified by the complete
E038/E042--E045 branch family. -/
theorem e058SpecialBrooksContradiction
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hG : Admissible G)
    (hclique : G.CliqueFree 6)
    (hindep : G.IndepSetFree 6) :
    False := by
  obtain ⟨relabeling, hregular', hG', hclique',
      hindep', hneighbor'⟩ :=
    exists_normalized_specialBrooks_graph
      G hregular hG hclique hindep
  exact e058NormalizedSpecialBrooksContradiction
    (relabelGraph G relabeling)
    hregular' hG' hclique' hindep' hneighbor'

theorem e058R5SpecialBrooksObstruction :
    R5SpecialBrooksObstruction := by
  intro G _ hregular hG hclique hindep
  exact e058SpecialBrooksContradiction
    G hregular hG hclique hindep

/-- Unconditional nonexistence of a fixed-`r=5` counterexample. -/
theorem e058NoR5Counterexample :
    ¬∃ χ : EdgeColoring (Fin 26) (Fin 5),
      IsCounterexample 6 χ :=
  no_r5_counterexample_of_special_brooks
    e058R5SpecialBrooksObstruction

/-- Unconditional fixed-`r=5` upper theorem. -/
theorem e058R5Upper : R5Upper :=
  r5Upper_of_special_brooks e058R5SpecialBrooksObstruction

/-- Erdős Problem 617 at the fixed value `r=5`. -/
theorem e058Problem617AtFive : Problem617At 5 :=
  problem617At_five_of_special_brooks
    e058R5SpecialBrooksObstruction

#print axioms e058R5SpecialBrooksObstruction
#print axioms e058NoR5Counterexample
#print axioms e058R5Upper
#print axioms e058Problem617AtFive
#check e058Problem617AtFive

end Erdos617

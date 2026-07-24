import Erdos617.Sat.SpecialBrooksE045Bridge
import E058SemanticE045Branch20Closure
import E058SemanticE045Branch21Closure
import E058SemanticE045Branch22Closure
import E058SemanticE045Branch23Closure
import E058SemanticE045Branch24Closure
import E058SemanticE045Branch25Closure

open Finset Fintype

namespace Erdos617

set_option maxHeartbeats 0 in
theorem e058E045Contradiction
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (branch : Fin 26) (hbranch : 20 ≤ branch)
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hG : Admissible G)
    (hclique : G.CliqueFree 6)
    (hindep : G.IndepSetFree 6)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (hanchor :
      G.neighborFinset 6 = r5FixedAnchorNeighbors)
    (hsorted :
      R5ComparisonsSorted G r5ZeroAnchorComparisons)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
        left right) :
    False := by
  have hcanonical :=
    r5CanonicalE045Units_allTrue
      G branch hneighbor hanchor horbit
  have hcases :
      branch = 20 ∨ branch = 21 ∨ branch = 22 ∨
      branch = 23 ∨ branch = 24 ∨ branch = 25 := by
    fin_cases branch <;> simp_all
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · apply E058SemanticE045Branch20Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE045Branch21Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE045Branch22Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE045Branch23Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE045Branch24Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE045Branch25Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide

set_option maxHeartbeats 0 in
theorem e058E045CanonicalContradiction
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (branch : Fin 26) (hbranch : 20 ≤ branch)
    (hregular : ∀ vertex, G.degree vertex = 5)
    (hG : Admissible G)
    (hclique : G.CliqueFree 6)
    (hindep : G.IndepSetFree 6)
    (hneighbor : G.neighborFinset 0 = r5FixedNeighbors)
    (horbit : ∀ left right : Fin 5,
      decide (G.Adj (r5NeighborVertex left)
        (r5NeighborVertex right)) =
      r5FiveVertexAdjacency
        (edgeVectorOfCode (r5NeighborhoodRepresentativeCode branch))
        left right) :
    False := by
  obtain ⟨relabeling, hregular', hG', hclique', hindep',
      hneighbor', hanchor', hsorted', horbit'⟩ :=
    exists_r5CanonicalE045Branch
      G branch hbranch hregular hG hclique hindep
      hneighbor horbit
  exact e058E045Contradiction
    (relabelGraph G relabeling) branch hbranch
    hregular' hG' hclique' hindep'
    hneighbor' hanchor' hsorted' horbit'

#print axioms e058E045CanonicalContradiction
#check e058E045CanonicalContradiction

end Erdos617

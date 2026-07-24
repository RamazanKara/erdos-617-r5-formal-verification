import E058E042DirectCoverage
import E058E043P04Coverage
import E058E043P09Coverage
import E058E043P19Coverage

open Finset Fintype

namespace Erdos617

/-- All twenty E042 cross-pattern children are impossible.  The three
exceptional children are discharged through their complete E043 quotients. -/
theorem e058E042Contradiction
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (child : Fin 20)
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
  by_cases h04 : child = 4
  · subst child
    exact e058E043P04CanonicalContradiction
      G hregular hG hclique hindep hneighbor horbit hcodes
  by_cases h09 : child = 9
  · subst child
    exact e058E043P09CanonicalContradiction
      G hregular hG hclique hindep hneighbor horbit hcodes
  by_cases h19 : child = 19
  · subst child
    exact e058E043P19CanonicalContradiction
      G hregular hG hclique hindep hneighbor horbit hcodes
  exact e058E042DirectContradiction
    G child h04 h09 h19 hregular hG hclique hindep
    hneighbor hsorted horbit hcodes

/-- Complete branch-19 contradiction, including the cross-pattern orbit
normalization and every direct or E043 child. -/
theorem e058E042CanonicalContradiction
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
        left right) :
    False := by
  obtain ⟨child, relabeling, hregular', hG', hclique',
      hindep', hneighbor', hsorted', horbit', hcodes'⟩ :=
    exists_r5CanonicalE042Child
      G hregular hG hclique hindep hneighbor horbit
  exact e058E042Contradiction
    (relabelGraph G relabeling) child
    hregular' hG' hclique' hindep'
    hneighbor' hsorted' horbit' hcodes'

#print axioms e058E042CanonicalContradiction
#check e058E042CanonicalContradiction

end Erdos617

import Erdos617.Sat.SpecialBrooksE043P04Bridge
import E058SemanticE043Parent04Child00Closure
import E058SemanticE043Parent04Child01Closure
import E058SemanticE043Parent04Child02Closure
import E058SemanticE043Parent04Child03Closure
import E058SemanticE043Parent04Child04Closure
import E058SemanticE043Parent04Child05Closure
import E058SemanticE043Parent04Child06Closure
import E058SemanticE043Parent04Child07Closure
import E058SemanticE043Parent04Child08Closure
import E058SemanticE043Parent04Child09Closure
import E058SemanticE043Parent04Child10Closure
import E058SemanticE043Parent04Child11Closure
import E058SemanticE043Parent04Child12Closure
import E058SemanticE043Parent04Child13Closure
import E058SemanticE043Parent04Child14Closure
import E058SemanticE043Parent04Child15Closure
import E058SemanticE043Parent04Child16Closure
import E058SemanticE043Parent04Child17Closure
import E058SemanticE043Parent04Child18Closure
import E058SemanticE043Parent04Child19Closure
import E058SemanticE043Parent04Child20Closure
import E058SemanticE043Parent04Child21Closure
import E058SemanticE043Parent04Child22Closure
import E058SemanticE043Parent04Child23Closure
import E058SemanticE043Parent04Child24Closure
import E058SemanticE043Parent04Child25Closure

open Finset Fintype

namespace Erdos617

set_option maxHeartbeats 800000 in
-- Twenty-six finite unit-list inclusions are discharged after splitting `child`.
set_option maxRecDepth 10000 in
theorem e058E043P04Contradiction
    (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (child : Fin 26)
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
        r5CrossPatternSortedCode 4 row)
    (hanchor : ∀ offset : Fin 19,
      decide (G.Adj 6
        ⟨(offset : Nat) + 7, by omega⟩) =
      r5P04AnchorTargetBit child offset) :
    False := by
  have hcanonical :=
    r5CanonicalE043P04Units_allTrue
      G child hneighbor horbit hcodes hanchor
  fin_cases child
  · apply E058SemanticE043Parent04Child00Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child01Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child02Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child03Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child04Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child05Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child06Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child07Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child08Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child09Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child10Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child11Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child12Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child13Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child14Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child15Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child16Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child17Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child18Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child19Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child20Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child21Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child22Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child23Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child24Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide
  · apply E058SemanticE043Parent04Child25Contradiction G
    refine ⟨hregular, hG, hclique, hindep, hsorted, ?_⟩
    apply R5NamedClause.AllTrue.of_subset G hcanonical
    decide

set_option maxHeartbeats 800000 in
-- The canonical bridge composes two finite permutations.
set_option maxRecDepth 10000 in
theorem e058E043P04CanonicalContradiction
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
        r5CrossPatternSortedCode 4 row) :
    False := by
  obtain ⟨child, relabeling, hregular', hG', hclique',
      hindep', hneighbor', hsorted', horbit', hcodes',
      hanchor'⟩ :=
    exists_r5CanonicalE043P04Child
      G hregular hG hclique hindep hneighbor horbit hcodes
  exact e058E043P04Contradiction
    (relabelGraph G relabeling) child
    hregular' hG' hclique' hindep'
    hneighbor' hsorted' horbit' hcodes' hanchor'

#print axioms e058E043P04CanonicalContradiction
#check e058E043P04CanonicalContradiction

end Erdos617

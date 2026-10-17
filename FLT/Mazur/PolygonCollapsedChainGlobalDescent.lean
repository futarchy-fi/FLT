/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedChainOverlapCover
public import FLT.Mazur.PolygonCollapsedChainEdgeDescent

/-!
# Gluing arbitrary-target maps on the full collapsed chain

The Laurent cover proves compatibility on whole Cartesian intersections.
Endpoint-compatible component maps therefore give a global chain morphism.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainGlobalDescent
open PolygonCollapsedChainOpenCover PolygonCollapsedChainLocalDescent
open PolygonCollapsedChainCartesianAtlas PolygonCollapsedChainOverlapEdges
open PolygonCollapsedChainEdgeDescent
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n) {Y : Scheme}
  (f : (j : Fin n) → j ≠ i → (ProjectiveLine.scheme K ⟶ Y))
  (w : ∀ (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i),
    ProjectiveLine.zero K ≫ f j hj = ProjectiveLine.infinity K ≫ f (finRotate n j) hs)

/-- Local descents agree on the entire intersection, not just its reduced support. -/
theorem compatible (a b : ChartIndex n i) :
    pullback.fst (chartMap K n h i a) (chartMap K n h i b) ≫ localMap K n i f w h a =
      pullback.snd _ _ ≫ localMap K n i f w h b := by
  by_cases he : a = b
  · subst b
    have he : pullback.fst (chartMap K n h i a) (chartMap K n h i a) =
        pullback.snd (chartMap K n h i a) (chartMap K n h i a) :=
      (cancel_mono (chartMap K n h i a)).mp pullback.condition
    rw [he]
  · apply (PolygonCollapsedChainOverlapCover.cover K n h i a b he).hom_ext
    intro e
    rcases e with e | e
    · change forward K n h i a b e.val e.property ≫ _ =
        forward K n h i a b e.val e.property ≫ _
      rw [forward_fst_assoc, forward_snd_assoc, firstEdge_localMap, secondEdge_localMap]
    · change reverse K n h i a b e.val e.property ≫ _ =
        reverse K n h i a b e.val e.property ≫ _
      rw [reverse_fst_assoc, reverse_snd_assoc, secondEdge_localMap, firstEdge_localMap]

/-- The global descent constructed from the actual full boundary and interior atlas. -/
irreducible_def desc : PolygonCollapsedChainModel.chain K n h i ⟶ Y :=
  (cover K n h i).glueMorphisms (localMap K n i f w h) (compatible K n h i f w)

@[reassoc] theorem chartMap_desc (a : ChartIndex n i) :
    chartMap K n h i a ≫ desc K n h i f w = localMap K n i f w h a := by
  rw [desc_def]
  exact (cover K n h i).ι_glueMorphisms _ _ a

/-- The glued map is the only global map with these full-chart restrictions. -/
theorem desc_unique (d : PolygonCollapsedChainModel.chain K n h i ⟶ Y)
    (hd : ∀ a, chartMap K n h i a ≫ d = localMap K n i f w h a) :
    d = desc K n h i f w := by
  apply (cover K n h i).hom_ext
  intro a
  exact (hd a).trans (chartMap_desc K n h i f w a).symm

end FLT.Mazur.PolygonCollapsedChainGlobalDescent

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineOverlapChartCommonRefinement

/-!
# Common overlap charts cover the intersection of their images

The affine cover of the fiber product supplies an open cover of the
intersection in the geometric base overlap. No affine-intersection assumption is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {A B : CommRingCat.{u}}
variable (f : Spec A ⟶ C.baseOverlap C') (g : Spec B ⟶ C.baseOverlap C')
variable [IsOpenImmersion f] [IsOpenImmersion g]

/-- Each constructed common chart is open in the geometric overlap. -/
instance overlapChartCommonMap_isOpenImmersion (i : (C.overlapChartCommonCover C' f g).I₀) :
    IsOpenImmersion (C.overlapChartCommonMap C' f g i) := by
  dsimp only [overlapChartCommonMap]
  infer_instance

/-- Images of the constructed common charts cover the intersection of the original images. -/
theorem overlapChartCommonMap_covers (x : C.baseOverlap C')
    (hx : x ∈ f.opensRange ⊓ g.opensRange) :
    ∃ i, x ∈ (C.overlapChartCommonMap C' f g i).opensRange := by
  have hx' : x ∈ Set.range (Limits.pullback.fst f g ≫ f) := by
    rw [IsOpenImmersion.range_pullback_to_base_of_left]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  obtain ⟨i, z, hz⟩ := C.overlapChartCommonCover_covers C' f g y
  refine ⟨i, z, ?_⟩
  change (Limits.pullback.fst f g ≫ f) ((C.overlapChartCommonCover C' f g).f i z) = _
  rw [hz]

end FLT.Mazur.SchemeAffineDescent.Chart

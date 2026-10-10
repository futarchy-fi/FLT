/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleLastPair
public import FLT.Mazur.WeierstrassInfinityTripleIntermediateTorsion

/-!
# Flat transport from the genuine inner addition domains

Both maps from the full intersection to an inner infinity-law domain are flat.
Thus the remaining regularity problem lies in the explicit two-input addition
algebra, rather than in global sections of the possibly nonaffine intersection.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The open inclusion preserves the original left chart input. -/
@[reassoc] theorem infinityAdditionInclusion_left :
    infinityAdditionInclusion W ≫
        Spec.map (CommRingCat.ofHom (chartProductLeft W 1 1).toRingHom) =
      Spec.map (CommRingCat.ofHom (infinityInputLeft W).toRingHom) := by
  rw [infinityAdditionInclusion, ← Spec.map_comp]
  rfl

/-- The open inclusion preserves the original right chart input. -/
@[reassoc] theorem infinityAdditionInclusion_right :
    infinityAdditionInclusion W ≫
        Spec.map (CommRingCat.ofHom (chartProductRight W 1 1).toRingHom) =
      Spec.map (CommRingCat.ofHom (infinityInputRight W).toRingHom) := by
  rw [infinityAdditionInclusion, ← Spec.map_comp]
  rfl

/-- The last-pair chart projection is the actual last inner domain inclusion. -/
theorem infinityTripleFullInputChart_lastPair :
    infinityTripleFullInputChart W hΔ ≫ infinityInputTripleLastPair W =
      infinityTripleFullLast W hΔ ≫ infinityAdditionInclusion W := by
  apply infinityProductSpec_hom_ext
  · rw [Category.assoc, infinityInputTripleLastPair_left,
      infinityTripleFullInputChart_second, Category.assoc, infinityAdditionInclusion_left]
    exact (infinityTripleFull_inputRelations W hΔ).1
  · rw [Category.assoc, infinityInputTripleLastPair_right,
      infinityTripleFullInputChart_third, Category.assoc, infinityAdditionInclusion_right]

/-- The first genuine inner-law projection is flat. -/
instance infinityTripleFullFirst_flat : Flat (infinityTripleFullFirst W hΔ) := by
  apply MorphismProperty.of_postcomp @Flat _ (infinityAdditionInclusion W)
    (inferInstance : IsOpenImmersion _)
  rw [← infinityTripleFullInputChart_pair]
  infer_instance

/-- The last genuine inner-law projection is flat. -/
instance infinityTripleFullLast_flat : Flat (infinityTripleFullLast W hΔ) := by
  apply MorphismProperty.of_postcomp @Flat _ (infinityAdditionInclusion W)
    (inferInstance : IsOpenImmersion _)
  rw [← infinityTripleFullInputChart_lastPair]
  infer_instance

/-- Regularity of the explicit law's output transports to both actual intermediate sums. -/
theorem infinityTripleIntermediateDenominator_regular_of_law
    (h : IsRegular (infinityAdditionChart W (coord W 1 2))) :
    IsRegular (infinityTripleIntermediateDenominator W hΔ) := by
  have hl := specSectionHom_isRegular (infinityTripleFullFirst W hΔ) h
  have hr := specSectionHom_isRegular (infinityTripleFullLast W hΔ) h
  exact hl.mul hr

/-- Regularity on the two-input addition algebra suffices for full infinity associativity. -/
theorem infinityTripleFull_assoc_of_law_output_regular
    (h : IsRegular (infinityAdditionChart W (coord W 1 2))) :
    infinityTripleFullMap W hΔ ≫ integralCurveTripleAddLeft W hΔ =
      infinityTripleFullMap W hΔ ≫ integralCurveTripleAddRight W hΔ :=
  infinityTripleFull_assoc_of_intermediate_regular W hΔ
    (infinityTripleIntermediateDenominator_regular_of_law W hΔ h)

end FLT.Mazur.WeierstrassIntegralChart

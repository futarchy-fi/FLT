/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothGoodReductionAddition
public import FLT.Mazur.WeierstrassSmoothGroup
public import FLT.Mazur.WeierstrassIntegralGroup

/-!
# The good-reduction comparison is a commutative group isomorphism

The inclusion of the entire relative smooth locus preserves the constructed
operations. For unit discriminant it is an isomorphism onto the original cubic.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual inclusion of the full smooth locus, as a morphism over the base. -/
def integralSmoothOverInclusion : integralSmoothOver W ⟶ integralCurveOver W :=
  Over.homMk (integralSmoothOpen W).ι rfl

/-- Pairing the smooth inclusions recovers the original inclusion of smooth factors. -/
theorem integralSmoothOverInclusion_tensor :
    (integralSmoothOverInclusion W ⊗ₘ integralSmoothOverInclusion W).left =
      smoothFactorsInclusion W := by
  apply pullback.hom_ext
  · exact (Over.tensorHom_left_fst _ _ _ _).trans (pullback.lift_fst _ _ _).symm
  · exact (Over.tensorHom_left_snd _ _ _ _).trans (pullback.lift_snd _ _ _).symm

/-- The smooth inclusion preserves the original zero section. -/
theorem integralSmoothOverInclusion_zero :
    integralSmoothOverZero W ≫ integralSmoothOverInclusion W = integralCurveOverZero W := by
  apply Over.OverMorphism.ext
  exact integralSmoothZero_inclusion W

/-- The smooth inclusion preserves the original negation. -/
theorem integralSmoothOverInclusion_negation :
    integralSmoothOverNegation W ≫ integralSmoothOverInclusion W =
      integralSmoothOverInclusion W ≫ integralCurveOverNegation W := by
  apply Over.OverMorphism.ext
  exact integralSmoothNegation_inclusion W

variable (hΔ : IsUnit W.Δ)

/-- The smooth inclusion intertwines the two independently constructed addition laws. -/
theorem integralSmoothOverInclusion_addition :
    integralSmoothOverAddition W ≫ integralSmoothOverInclusion W =
      (integralSmoothOverInclusion W ⊗ₘ integralSmoothOverInclusion W) ≫
        integralCurveOverAddition W hΔ := by
  apply Over.OverMorphism.ext
  change smoothFactorAddition W ≫ (integralSmoothOpen W).ι =
    (integralSmoothOverInclusion W ⊗ₘ integralSmoothOverInclusion W).left ≫ _
  rw [integralSmoothOverInclusion_tensor]
  exact smoothFactorAddition_goodReduction W hΔ

/-- In good reduction, the actual smooth inclusion is an isomorphism over the base. -/
theorem integralSmoothOverInclusion_isIso (hΔ : IsUnit W.Δ) :
    IsIso (integralSmoothOverInclusion W) := by
  let _ := integralCurveStructure_smooth W hΔ
  have hi : IsIso (integralSmoothOpen W).ι := by
    change IsIso (integralCurveStructure W).smoothLocus.ι
    rw [Scheme.Hom.smoothLocus_eq_top]
    exact (integralCurve W).topIso.isIso_hom
  have : IsIso ((Over.forget (Spec (.of R))).map (integralSmoothOverInclusion W)) := hi
  exact isIso_of_reflects_iso _ (Over.forget (Spec (.of R)))

/-- The full smooth group is canonically the existing integral group in good reduction. -/
def integralSmoothGoodReductionGroupIso : integralSmoothGroup W ≅ integralCurveGroup W hΔ := by
  let _ := integralSmoothOverInclusion_isIso W hΔ
  exact CommGrp.mkIso (asIso (integralSmoothOverInclusion W))
    (integralSmoothOverInclusion_zero W) (integralSmoothOverInclusion_addition W hΔ)

/-- The group isomorphism has the original open inclusion as underlying scheme morphism. -/
theorem integralSmoothGoodReductionGroupIso_hom :
    (integralSmoothGoodReductionGroupIso W hΔ).hom.hom.hom.hom.left =
      (integralSmoothOpen W).ι := rfl

end FLT.Mazur.WeierstrassIntegralChart

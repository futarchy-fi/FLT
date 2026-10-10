/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRelativeSmoothOpen
public import FLT.Mazur.WeierstrassIntegralZeroSection

/-!
# The zero section lies in the relative smooth locus

The Z derivative at [0:1:0] is one over every coefficient ring. Thus the
original zero section lifts through a proved smooth derivative chart, with
no good-reduction hypothesis.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- At infinity the Z derivative equals one over the original ring. -/
@[simp] theorem chartInfinityEvaluation_partial :
    chartInfinityEvaluation (S := R) W (chartPartial W 1 2) = 1 := by
  rw [chartPartial_map]
  change MvPolynomial.eval _ (W.map (algebraMap R R)).toProjective.polynomialZ = 1
  rw [WeierstrassCurve.Projective.eval_polynomialZ]
  simp [chartInfinityEvaluation_coord]

/-- Infinity evaluation extends through the actual Z-derivative localization. -/
def smoothZeroEvaluation : Localization.Away (chartPartial W 1 2) →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (chartPartial W 1 2)
    (show IsUnit (chartInfinityEvaluation (S := R) W (chartPartial W 1 2)) by
      rw [chartInfinityEvaluation_partial]; exact isUnit_one)

/-- The localized evaluation recovers the original infinity evaluation. -/
theorem smoothZeroEvaluation_restriction :
    (smoothZeroEvaluation W).toRingHom.comp
      (algebraMap (Coordinate W 1) (Localization.Away (chartPartial W 1 2))) =
        (chartInfinityEvaluation (S := R) W).toRingHom := by
  apply RingHom.ext
  intro a
  exact IsLocalization.Away.lift_eq (chartPartial W 1 2)
    (show IsUnit (chartInfinityEvaluation (S := R) W (chartPartial W 1 2)) by
      rw [chartInfinityEvaluation_partial]; exact isUnit_one) a

/-- The original zero section factors through the relative smooth open. -/
def integralSmoothZero : Spec (.of R) ⟶ (integralSmoothOpen W).toScheme :=
  Spec.map (CommRingCat.ofHom (smoothZeroEvaluation W).toRingHom) ≫
    chartPartialToSmooth W 1 2 (by decide)

/-- The smooth zero section is the original cubic zero section after inclusion. -/
@[reassoc (attr := simp)] theorem integralSmoothZero_inclusion :
    integralSmoothZero W ≫ (integralSmoothOpen W).ι = integralCurveZero W := by
  rw [integralSmoothZero, Category.assoc, chartPartialToSmooth_inclusion,
    ← Category.assoc]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((smoothZeroEvaluation W).toRingHom.comp
    (algebraMap _ _))) ≫ integralCurveChart W 1 = _
  rw [smoothZeroEvaluation_restriction]
  rfl

/-- This is a section over the entire original coefficient scheme. -/
@[reassoc] theorem integralSmoothZero_structure :
    integralSmoothZero W ≫ integralSmoothStructure W = 𝟙 _ := by
  rw [integralSmoothStructure, ← Category.assoc, integralSmoothZero_inclusion,
    integralCurveZero_structure]

/-- The original zero section has image in the actual smooth locus in every reduction type. -/
theorem integralCurveZero_range_smooth :
    Set.range (integralCurveZero W) ⊆ integralSmoothOpen W := by
  rw [← integralSmoothZero_inclusion]
  rintro _ ⟨x, rfl⟩
  exact (integralSmoothZero W x).property

end FLT.Mazur.WeierstrassIntegralChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineEquationPullback
public import FLT.Mazur.WeierstrassCoefficientPresentationRefinement

/-!
# Full coefficient coherence on affine normalized refinements

The extracted coefficient maps and named long equations give a commuting
square of actual generalized-curve presentations on every affine refinement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.CyclicCharacteristicAtlas
open WeierstrassIntegralChart GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool) {A B : Type} [CommRing A] [CommRing B]
  (q : Spec (.of A) ⟶ normalizedLocus n b) (f : A →+* B)
local notation "k" => Spec.map (CommRingCat.ofHom f)
local notation "v" => Spec.map (CommRingCat.ofHom (affineCoefficientHom n b q))
local notation "w" => Spec.map (CommRingCat.ofHom (affineCoefficientHom n b (k ≫ q)))

/-- The spectrum map on a refined affine coefficient chart is the exact composite. -/
theorem affineCoefficientSpec_refine : w = k ≫ v :=
  (congrArg (fun t ↦ Spec.map (CommRingCat.ofHom t))
    (affineCoefficientHom_pullback n b q f)).trans (Spec.map_comp _ _)

/-- The existing affine-model refinement is the named full coefficient presentation. -/
theorem affineModelPullbackIso_eq_presentation : affineModelPullbackIso n b q f =
    coefficientPresentationIso (affineEquation n b q) (affineEquation_discriminant n b q) f
      (affineEquation n b (k ≫ q)) (affineEquation_discriminant n b (k ≫ q))
        (affineEquation_pullback n b q f) := rfl

/-- The concrete affine coefficient square commutes before transport to the original family. -/
theorem affineCoefficientModel_refine :
    (coefficientModelIso (coefficientEquation b) (coefficientEquation_unit b)
      (affineCoefficientHom n b (k ≫ q))).hom ≫
        ((coefficientModel b).baseChangeCompEqIso v k w
          (affineCoefficientSpec_refine n b q f)).hom =
      (affineModelPullbackIso n b q f).hom ≫
        baseChangeMap k (coefficientModelIso (coefficientEquation b)
          (coefficientEquation_unit b) (affineCoefficientHom n b q)).hom := by
  rw [affineModelPullbackIso_eq_presentation]
  exact coefficientPresentationIso_refine (coefficientEquation b)
    (affineEquation n b q) (affineEquation n b (k ≫ q))
    (coefficientEquation_unit b) (affineEquation_discriminant n b q)
    (affineEquation_discriminant n b (k ≫ q))
    (affineCoefficientHom n b q) f (affineCoefficientHom n b (k ≫ q))
    (affineCoefficientHom_pullback n b q f) rfl (affineEquation_pullback n b q f) rfl

end FLT.Mazur.CyclicCharacteristicAtlas

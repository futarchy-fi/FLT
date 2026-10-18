/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineEquation

/-!
# Affine chart equations under arbitrary coefficient base change

Refining an affine chart gives the coefficient pullback of the original
long equation. This is an equality of all coefficients and a full model
isomorphism, with no characteristic or etaleness restriction.
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

/-- Affine refinement retains exactly the composite original coefficient homomorphism. -/
theorem affineCoefficientHom_pullback :
    affineCoefficientHom n b (k ≫ q) = f.comp (affineCoefficientHom n b q) := by
  apply CommRingCat.hom_ext_iff.mp
  apply Spec.map_injective
  change Spec.map (Spec.preimage ((k ≫ q) ≫ normalizedCoefficientMap n b)) =
    Spec.map (CommRingCat.ofHom (affineCoefficientHom n b q) ≫ CommRingCat.ofHom f)
  rw [Spec.map_preimage, Spec.map_comp, affineCoefficientHom_spec, Category.assoc]

/-- All five long coefficients commute with every affine chart refinement. -/
theorem affineEquation_pullback :
    affineEquation n b (k ≫ q) = (affineEquation n b q).map f := by
  unfold affineEquation
  rw [affineCoefficientHom_pullback, WeierstrassCurve.map_map]

/-- Refining the affine presentation is the actual coefficient pullback of its full model. -/
def affineModelPullbackIso :
    integralGeneralizedEllipticCurve (affineEquation n b (k ≫ q))
        (affineEquation_discriminant n b (k ≫ q)) ≅
      (integralGeneralizedEllipticCurve (affineEquation n b q)
        (affineEquation_discriminant n b q)).baseChange k := by
  have he : integralGeneralizedEllipticCurve (affineEquation n b (k ≫ q))
      (affineEquation_discriminant n b (k ≫ q)) =
      integralGeneralizedEllipticCurve ((affineEquation n b q).map f)
        (coefficientEquation_discriminant _ (affineEquation_discriminant n b q) f) := by
    congr 1
    exact affineEquation_pullback n b q f
  exact eqToIso he ≪≫ coefficientModelIso _ (affineEquation_discriminant n b q) f

end FLT.Mazur.CyclicCharacteristicAtlas

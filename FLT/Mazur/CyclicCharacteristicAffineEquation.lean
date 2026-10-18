/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicCoefficientBase
public import FLT.Mazur.WeierstrassCoefficientGeneralizedIso

/-!
# Affine Weierstrass presentations of the original normalized families

Every affine map into either normalized chart has a concrete long equation.
The full generalized curve comparison is constructed from its coefficient map,
including the original group and action, without changing the modular object.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.CyclicCharacteristicAtlas
open WeierstrassIntegralChart GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool) {A : Type} [CommRing A]
  (q : Spec (.of A) ⟶ normalizedLocus n b)

/-- Extract the actual coefficient homomorphism from an affine normalized test. -/
def affineCoefficientHom : CoefficientRing b →+* A :=
  (Spec.preimage (q ≫ normalizedCoefficientMap n b)).hom

/-- The extracted homomorphism gives exactly the original composite base map. -/
theorem affineCoefficientHom_spec :
    Spec.map (CommRingCat.ofHom (affineCoefficientHom n b q)) =
      q ≫ normalizedCoefficientMap n b :=
  Spec.map_preimage _

/-- The concrete long Weierstrass equation of an affine normalized family. -/
def affineEquation : WeierstrassCurve A :=
  (coefficientEquation b).map (affineCoefficientHom n b q)

/-- No extra localization is needed to obtain smoothness on the affine chart. -/
theorem affineEquation_discriminant : IsUnit (affineEquation n b q).Δ :=
  coefficientEquation_discriminant _ (coefficientEquation_unit b) _

/-- The actual affine model compares with the original normalized full family. -/
def affineEquationIso :
    integralGeneralizedEllipticCurve (affineEquation n b q) (affineEquation_discriminant n b q) ≅
      (normalizedCurve n b).baseChange q :=
  coefficientModelIso _ (coefficientEquation_unit b) (affineCoefficientHom n b q) ≪≫
    (baseChangeCongr (affineCoefficientHom_spec n b q)).app _ ≪≫
    (coefficientModel b).baseChangeCompIso (normalizedCoefficientMap n b) q ≪≫
    (baseChangeFunctor q).mapIso (normalizedCoefficientIso n b)

end FLT.Mazur.CyclicCharacteristicAtlas

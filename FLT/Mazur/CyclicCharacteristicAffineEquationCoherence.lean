/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineCoefficientCoherence
public import FLT.Mazur.GeneralizedPresentationRefinement

/-!
# Affine refinement coherence for the original normalized families

The affine equation isomorphism on a refined chart is the coefficient
refinement followed by pullback of the original affine equation isomorphism.
This is equality in the full generalized-curve category.
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

/-- The existing affine equation isomorphism is transport through the coefficient base. -/
theorem affineEquationIso_eq_throughBase : affineEquationIso n b q =
    presentationThroughBase (coefficientModel b) (normalizedCoefficientMap n b) q
      (Spec.map (CommRingCat.ofHom (affineCoefficientHom n b q)))
      (affineCoefficientHom_spec n b q) (normalizedCoefficientIso n b)
      (coefficientModelIso (coefficientEquation b) (coefficientEquation_unit b)
        (affineCoefficientHom n b q)) := by
  apply Iso.ext
  simp only [affineEquationIso, presentationThroughBase, baseChangeCompEqIso,
    Iso.trans_hom, Category.assoc]
  rfl

/-- Full affine presentations commute with every coefficient refinement. -/
theorem affineEquationIso_refine :
    (affineEquationIso n b (k ≫ q)).hom ≫
      ((normalizedCurve n b).baseChangeCompIso q k).hom =
    (affineModelPullbackIso n b q f).hom ≫ baseChangeMap k (affineEquationIso n b q).hom := by
  rw [affineEquationIso_eq_throughBase, affineEquationIso_eq_throughBase]
  exact presentationThroughBase_refine (coefficientModel b) (normalizedCoefficientMap n b)
    q k (Spec.map (CommRingCat.ofHom (affineCoefficientHom n b q)))
    (Spec.map (CommRingCat.ofHom (affineCoefficientHom n b (k ≫ q))))
    (affineCoefficientHom_spec n b q) (affineCoefficientSpec_refine n b q f)
    (normalizedCoefficientIso n b)
    (coefficientModelIso (coefficientEquation b) (coefficientEquation_unit b)
      (affineCoefficientHom n b q))
    (coefficientModelIso (coefficientEquation b) (coefficientEquation_unit b)
      (affineCoefficientHom n b (k ≫ q)))
    (affineModelPullbackIso n b q f) (affineCoefficientModel_refine n b q f)

/-- Refinement coherence also holds as an equality of full isomorphisms. -/
theorem affineEquationIso_refine_iso :
    affineEquationIso n b (k ≫ q) ≪≫ (normalizedCurve n b).baseChangeCompIso q k =
      affineModelPullbackIso n b q f ≪≫ (baseChangeFunctor k).mapIso (affineEquationIso n b q) :=
  Iso.ext (affineEquationIso_refine n b q f)

end FLT.Mazur.CyclicCharacteristicAtlas

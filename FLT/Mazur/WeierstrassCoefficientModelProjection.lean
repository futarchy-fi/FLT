/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassCoefficientGeneralizedIso
public import FLT.Mazur.WeierstrassProperCoefficientComposition

/-!
# Full coefficient comparisons retain the proper coefficient morphism

The extension from the smooth group has the original proper map on the entire
curve. Named specialized equations retain their equality transports.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] coefficientModelIso coefficientModelGroupIso
  integralCurveCoefficientBaseChangeIso
variable {R A : Type} [CommRing R] [CommRing A]
  (W : WeierstrassCurve R) (hW : IsUnit W.Δ) (f : R →+* A)

/-- The full comparison projects to the actual proper coefficient morphism. -/
@[reassoc] theorem coefficientModelIso_fst :
    (coefficientModelIso W hW f).hom.curve.left ≫
      pullback.fst (integralCurveStructure W) (Spec.map (CommRingCat.ofHom f)) =
        properCoefficientMap W (W.map f) f rfl := by
  let _ : Algebra R A := f.toAlgebra
  have h := (coefficientModelIso W hW f).hom.inclusion
  rw [integralGeneralizedEllipticCurve_inclusion, baseChange_inclusion] at h
  change (𝟙 _) ≫ _ = _ ≫ (Over.pullback _).map
    (integralGeneralizedEllipticCurve W hW).inclusion at h
  rw [integralGeneralizedEllipticCurve_inclusion] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h
  rw [congrArg (fun z ↦ z.left) h, coefficientModelIso_group]
  unfold coefficientModelGroupIso
  change (integralCurveCoefficientGroupIso W hW
    (coefficientEquation_discriminant W hW f)).hom.hom.hom.hom.left ≫ _ = _
  rw [integralCurveCoefficientGroupIso_hom]
  exact (integralCurveCoefficientBaseChangeIso_fst W).trans (Category.id_comp _).symm

variable (V : WeierstrassCurve A) (hV : IsUnit V.Δ) (h : V = W.map f)

/-- A named specialized equation compares with the original full coefficient pullback. -/
def coefficientPresentationIso :
    integralGeneralizedEllipticCurve V hV ≅
      (integralGeneralizedEllipticCurve W hW).baseChange
        (Spec.map (CommRingCat.ofHom f)) :=
  eqToIso (by cases h; rfl) ≪≫ coefficientModelIso W hW f

/-- Equation transport keeps the exact original proper coefficient map. -/
@[reassoc] theorem coefficientPresentationIso_fst :
    (coefficientPresentationIso W hW f V hV h).hom.curve.left ≫
      pullback.fst (integralCurveStructure W) (Spec.map (CommRingCat.ofHom f)) =
        properCoefficientMap W V f h := by
  subst V
  simpa only [coefficientPresentationIso, eqToIso_refl, Iso.refl_trans] using
    coefficientModelIso_fst W hW f

end FLT.Mazur.WeierstrassIntegralChart

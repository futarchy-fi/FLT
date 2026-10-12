/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryFixedCoefficientComparison

/-!
# The actual projection of an equation coefficient comparison

Equality transport of the specialized equation retains the original proper
coefficient map. No group operation is unfolded in this comparison.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]

/-- The proper coefficient projection, with the original equation equality retained. -/
def equationCoefficientProjection (W : WeierstrassCurve R) (f : ParameterRing →+* R)
    (he : W = smoothEquation.map f) : integralCurve W ⟶ integralCurve smoothEquation := by
  letI : Algebra ParameterRing R := f.toAlgebra
  exact eqToHom (congrArg integralCurve he) ≫ integralCoefficientMorphism smoothEquation

/-- Forgetting the coefficient group comparison gives the actual proper coefficient map. -/
@[reassoc] theorem equationCoefficientGroupIso_fst
    (W : WeierstrassCurve R) (hW : IsUnit W.Δ)
    (f : ParameterRing →+* R) (he : W = smoothEquation.map f) :
    (equationCoefficientGroupIso W hW f he).hom.hom.hom.hom.left ≫
        pullback.fst universalGroup.hom (Spec.map (CommRingCat.ofHom f)) =
      equationCoefficientProjection W f he := by
  subst W
  let _ : Algebra ParameterRing R := f.toAlgebra
  change (integralCurveCoefficientOverIso smoothEquation).hom.left ≫ _ =
    𝟙 _ ≫ integralCoefficientMorphism smoothEquation
  rw [Category.id_comp]
  exact integralCurveCoefficientOverIso_fst smoothEquation

/-- The inverse coefficient comparison recovers the original pullback projection. -/
@[reassoc] theorem equationCoefficientGroupIso_inv_projection
    (W : WeierstrassCurve R) (hW : IsUnit W.Δ)
    (f : ParameterRing →+* R) (he : W = smoothEquation.map f) :
    (equationCoefficientGroupIso W hW f he).inv.hom.hom.hom.left ≫
        equationCoefficientProjection W f he =
      pullback.fst universalGroup.hom (Spec.map (CommRingCat.ofHom f)) := by
  rw [← equationCoefficientGroupIso_fst W hW f he, ← Category.assoc]
  have h := congrArg (fun z ↦ z.hom.hom.hom.left)
    (equationCoefficientGroupIso W hW f he).inv_hom_id
  change (equationCoefficientGroupIso W hW f he).inv.hom.hom.hom.left ≫
    (equationCoefficientGroupIso W hW f he).hom.hom.hom.hom.left = 𝟙 _ at h
  rw [h, Category.id_comp]

end FLT.Mazur.UniversalWeierstrass

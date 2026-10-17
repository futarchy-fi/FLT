/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSpecializationGroup
public import FLT.Mazur.WeierstrassProperCoefficientComposition

/-!
# Proper projections of coefficient comparisons for named equations

Equality of equations and the coefficient group isomorphism retain the actual
proper coefficient morphism over an arbitrary coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S]

/-- Equation transport on group schemes is the actual transport of their proper curves. -/
theorem equationGroupIso_proper_hom {W V : WeierstrassCurve S} (h : W = V)
    (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) :
    (UniversalWeierstrass.equationGroupIso h hW hV).hom.hom.hom.hom.left =
      eqToHom (congrArg integralCurve h) := by
  subst V
  rfl

/-- A coefficient group comparison projects to the named proper coefficient morphism. -/
@[reassoc] theorem equationCoefficientComparison_fst
    (W : WeierstrassCurve R) (V : WeierstrassCurve S) (f : R →+* S)
    (h : V = W.map f) (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) :
    let _ : Algebra R S := f.toAlgebra
    let hd : IsUnit (W.map (algebraMap R S)).Δ := h ▸ hV
    ((UniversalWeierstrass.equationGroupIso h hV hd ≪≫
      integralCurveCoefficientGroupIso W hW hd).hom.hom.hom.hom.left) ≫
        pullback.fst (integralCurveGroup W hW).X.hom
          (Spec.map (CommRingCat.ofHom f)) = properCoefficientMap W V f h := by
  subst V
  let _ : Algebra R S := f.toAlgebra
  change (𝟙 _ ≫ (integralCurveCoefficientOverIso W).hom.left) ≫ _ =
    𝟙 _ ≫ integralCoefficientMorphism W
  rw [Category.id_comp, Category.id_comp]
  exact integralCurveCoefficientOverIso_fst W

end FLT.Mazur.WeierstrassIntegralChart

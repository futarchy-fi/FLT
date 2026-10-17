/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSpecializationGroup
public import FLT.Mazur.GroupSchemeBaseChangeComposition

/-!
# Coefficient group comparisons retain equation and parameter equalities

The comparison uses the given equation transport and actual coefficient map.
Changing both by equality commutes with the resulting group isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] integralCurveGroup integralCurveCoefficientGroupIso
variable {R S : Type} [CommRing R] [CommRing S]

/-- The group comparison for a named equation and a specified coefficient map. -/
def equationCoefficientComparison (W : WeierstrassCurve R) (hW : IsUnit W.Δ)
    (V : WeierstrassCurve S) (hV : IsUnit V.Δ) (f : R →+* S) (he : V = W.map f) :
    integralCurveGroup V hV ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapCommGrp.obj
        (integralCurveGroup W hW) := by
  let _ : Algebra R S := f.toAlgebra
  have hd : IsUnit (W.map (algebraMap R S)).Δ := he ▸ hV
  exact UniversalWeierstrass.equationGroupIso he hV hd ≪≫
    integralCurveCoefficientGroupIso W hW hd

/-- Actual coefficient comparisons commute with simultaneous equation and map equalities. -/
theorem equationCoefficientComparison_congr
    (W : WeierstrassCurve R) (hW : IsUnit W.Δ)
    (V Z : WeierstrassCurve S) (hV : IsUnit V.Δ) (hZ : IsUnit Z.Δ)
    (f k : R →+* S) (he : V = W.map f) (he' : Z = W.map k)
    (h : V = Z) (hk : f = k)
    (hg : integralCurveGroup V hV = integralCurveGroup Z hZ) :
    equationCoefficientComparison W hW V hV f he ≪≫
        GroupSchemeBaseChange.congrIso (congrArg (fun z ↦ Spec.map (CommRingCat.ofHom z)) hk)
          (integralCurveGroup W hW) =
      eqToIso hg ≪≫ equationCoefficientComparison W hW Z hZ k he' := by
  cases h
  cases hk
  simp only [GroupSchemeBaseChange.congrIso, eqToIso_refl, Iso.trans_refl, Iso.refl_trans]

end FLT.Mazur.WeierstrassIntegralChart

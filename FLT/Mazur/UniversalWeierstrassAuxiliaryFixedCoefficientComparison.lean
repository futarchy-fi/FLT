/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizationFixedGroup
public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedFixedCoordinates
public import FLT.Mazur.GroupSchemeBaseChangeComposition

/-!
# Coefficient comparisons agree on the normalized frame

The original and normalized coefficient comparisons agree after the actual
identity normalization. Equality transport retains their original coefficient
maps, rather than choosing a new presentation of the universal family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] integralCurveGroup integralCurveCoefficientGroupIso
variable {R : Type} [CommRing R]

/-- The coefficient comparison for an equation with a specified universal parameter. -/
def equationCoefficientGroupIso (W : WeierstrassCurve R) (hW : IsUnit W.Δ)
    (f : ParameterRing →+* R) (he : W = smoothEquation.map f) :
    integralCurveGroup W hW ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapCommGrp.obj
        (integralCurveGroup smoothEquation smoothEquation_discriminant) := by
  letI : Algebra ParameterRing R := f.toAlgebra
  have hd : IsUnit (smoothEquation.map (algebraMap ParameterRing R)).Δ := he ▸ hW
  have hg : integralCurveGroup W hW =
      integralCurveGroup (smoothEquation.map (algebraMap ParameterRing R)) hd := by
    congr 1
  exact eqToIso hg ≪≫
    integralCurveCoefficientGroupIso smoothEquation smoothEquation_discriminant hd

/-- Equation and parameter equalities commute with the actual coefficient comparison. -/
theorem equationCoefficientGroupIso_congr
    (W V : WeierstrassCurve R) (hW : IsUnit W.Δ) (hV : IsUnit V.Δ)
    (f k : ParameterRing →+* R) (he : W = smoothEquation.map f)
    (he' : V = smoothEquation.map k) (h : W = V) (hk : f = k)
    (hg : integralCurveGroup W hW = integralCurveGroup V hV) :
    equationCoefficientGroupIso W hW f he ≪≫
        GroupSchemeBaseChange.congrIso (congrArg (fun z ↦ Spec.map (CommRingCat.ofHom z)) hk)
          (integralCurveGroup smoothEquation smoothEquation_discriminant) =
      eqToIso hg ≪≫ equationCoefficientGroupIso V hV k he' := by
  cases h
  cases hk
  simp only [GroupSchemeBaseChange.congrIso, eqToIso_refl, Iso.trans_refl, Iso.refl_trans]

variable (g : AuxiliarySectionRing →+* R) (hn : SatisfiesNormalization g)

include hn in
/-- The original and normalized coefficient maps are equal on the actual slice. -/
theorem auxiliaryNormalizedCoefficientBase_fixed :
    auxiliaryNormalizedCoefficientBase g = auxiliaryCoefficientBase g := by
  exact congrArg (fun z ↦ Spec.map (CommRingCat.ofHom z))
    (auxiliaryNormalizedCoefficientHom_fixed g hn)

/-- The original coefficient comparison commutes with the full normalization group map. -/
theorem auxiliaryNormalizationGroupIso_coefficient_fixed :
    auxiliaryNormalizedCoefficientGroupIso g ≪≫
        GroupSchemeBaseChange.congrIso (auxiliaryNormalizedCoefficientBase_fixed g hn)
          (integralCurveGroup smoothEquation smoothEquation_discriminant) =
      auxiliaryNormalizationGroupIso g ≪≫ auxiliaryCoefficientGroupIso g := by
  rw [auxiliaryNormalizationGroupIso_fixed g hn]
  exact equationCoefficientGroupIso_congr _ _ _ _ _ _
    (auxiliaryNormalizedCoefficientHom_equation g).symm
    (auxiliaryPullbackEquation_coefficient g)
    (normalizedSlice_equation_fixed g hn)
    (auxiliaryNormalizedCoefficientHom_fixed g hn) (auxiliaryNormalizedGroup_fixed g hn)

end FLT.Mazur.UniversalWeierstrass

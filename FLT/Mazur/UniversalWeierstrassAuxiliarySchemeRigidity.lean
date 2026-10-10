/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryPullbackSections
public import FLT.Mazur.UniversalWeierstrassAuxiliaryCoordinateInverse
public import FLT.Mazur.UniversalWeierstrassAuxiliaryCoordinateUnits
public import FLT.Mazur.WeierstrassOriginAutomorphismFrame

/-!
# Rigidity of the actual auxiliary-marked scheme after arbitrary ring pullback

The three original markings indexed by (1,0), its inverse, and (0,1)
form the unit-separated frame. Fixing the actual scheme sections therefore
forces identity, without an admissible coordinate-change hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

variable {R : Type} [CommRing R] (g : AuxiliarySectionRing →+* R)

/-- An origin-preserving automorphism fixing the original auxiliary sections is identity. -/
theorem auxiliary_scheme_rigidity_after_pullback
    (e : integralCurve (auxiliaryPullbackEquation g) ≅ integralCurve (auxiliaryPullbackEquation g))
    (hb : e.hom ≫ integralCurveStructure (auxiliaryPullbackEquation g) =
      integralCurveStructure (auxiliaryPullbackEquation g))
    (hz : integralCurveZero (auxiliaryPullbackEquation g) ≫ e.hom =
      integralCurveZero (auxiliaryPullbackEquation g))
    (hf : ∀ (a : Labels 4) (ha : a ≠ 1),
      auxiliaryPullbackSection g a ha ≫ e.hom = auxiliaryPullbackSection g a ha) :
    e.hom = 𝟙 _ := by
  let a : Labels 4 := Multiplicative.ofAdd (1, 0)
  let b : Labels 4 := Multiplicative.ofAdd (0, 1)
  have ha : a ≠ 1 := by decide
  have hb' : b ≠ 1 := by decide
  have hab : a ≠ b := by decide
  have hab' : a ≠ b⁻¹ := by decide
  have han : a ≠ a⁻¹ := by decide
  apply originAut_eq_id_of_frame _ (auxiliaryPullbackEquation_discriminant g) e hb hz
    (auxiliaryPullbackEvaluation g a ha)
    (auxiliaryPullbackEvaluation g a⁻¹ (inv_ne_one.mpr ha))
    (auxiliaryPullbackEvaluation g b hb')
    (by simpa only [auxiliaryPullbackSection, Category.assoc] using hf a ha)
    (by simpa only [auxiliaryPullbackSection, Category.assoc] using
      hf a⁻¹ (inv_ne_one.mpr ha))
    (by simpa only [auxiliaryPullbackSection, Category.assoc] using hf b hb')
  · simp only [auxiliaryPullbackEvaluation_coord, auxiliaryCoordinate_inverse_x a ha]
  · simpa only [auxiliaryPullbackEvaluation_coord, map_sub] using
      (auxiliaryCoordinate_x_sub_isUnit a b ha hb' hab hab').map g
  · simpa only [auxiliaryPullbackEvaluation_coord, auxiliaryCoordinate_inverse_y a ha, map_sub]
      using (auxiliaryCoordinate_y_sub_neg_isUnit a ha han).map g

end FLT.Mazur.UniversalWeierstrass

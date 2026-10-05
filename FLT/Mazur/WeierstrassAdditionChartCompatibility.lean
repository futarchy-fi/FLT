/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.PointReductionAddition
public import FLT.Mazur.WeierstrassIntegralAdditionCharts

/-!
# Compatibility of the two regular integral addition charts

Over any common algebra of the two principal opens, the two regular slopes
coincide and the resulting maps from the cubic coordinate algebra agree.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)
  (f : SecantChart W →ₐ[R] S) (g : TangentChart W →ₐ[R] S)

/-- Both regular slopes agree on every common restriction of their principal opens. -/
theorem slope_chart_compatibility
    (hbase : f.comp (secantRestriction W) = g.comp (tangentRestriction W)) :
    f (secantSlope W) = g (tangentSlope W) := by
  have hb (a) : f (secantRestriction W a) = g (tangentRestriction W a) :=
    DFunLike.congr_fun hbase a
  have hu := (IsLocalization.Away.algebraMap_isUnit (secantDenominator W)
    (S := SecantChart W)).map f
  change IsUnit (f (secantRestriction W (secantDenominator W))) at hu
  simp only [secantDenominator, map_sub, hb] at hu
  have hs := congrArg f (secantSlope_relation W)
  have ht := congrArg g (tangentSlope_line W)
  simp only [map_mul, map_sub, hb] at hs
  simp only [map_mul, map_sub] at ht
  exact hu.mul_left_inj.mp (hs.trans ht.symm)

/-- The regular addition maps agree on every common restriction of the slope charts. -/
theorem addition_chart_compatibility
    (hbase : f.comp (secantRestriction W) = g.comp (tangentRestriction W)) :
    f.comp (secantAddition W) = g.comp (tangentAddition W) := by
  have hb (a) : f (secantRestriction W a) = g (tangentRestriction W a) :=
    DFunLike.congr_fun hbase a
  have hs := slope_chart_compatibility W f g hbase
  apply hom_ext
  intro i
  change f (secantAddition W (coord W 2 i)) = g (tangentAddition W (coord W 2 i))
  rw [secantAddition_coord, tangentAddition_coord]
  fin_cases i
  · change f ((W.map (algebraMap R (SecantChart W))).toAffine.addX _ _ _) =
      g ((W.map (algebraMap R (TangentChart W))).toAffine.addX _ _ _)
    simp only [Affine.addX, map_sub, map_add, map_pow, map_mul, map_a₁, map_a₂,
      AlgHom.commutes, hb, hs]
  · change f ((W.map (algebraMap R (SecantChart W))).toAffine.addY _ _ _ _) =
      g ((W.map (algebraMap R (TangentChart W))).toAffine.addY _ _ _ _)
    simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX, map_neg,
      map_sub, map_add, map_pow, map_mul, map_a₁, map_a₂, map_a₃, AlgHom.commutes, hb, hs]
  · change f 1 = g 1
    rw [map_one, map_one]

variable {K : Type*} [Field K] [Algebra R K] [DecidableEq K]

/-- The regular secant slope specializes to the slope used by the field point law. -/
theorem secantSlope_field (fK : SecantChart W →ₐ[R] K) :
    fK (secantSlope W) = (W.map (algebraMap R K)).toAffine.slope
      (fK (secantRestriction W (productX₁ W))) (fK (secantRestriction W (productX₂ W)))
      (fK (secantRestriction W (productY₁ W))) (fK (secantRestriction W (productY₂ W))) := by
  have hu := (IsLocalization.Away.algebraMap_isUnit (secantDenominator W)
    (S := SecantChart W)).map fK
  change IsUnit (fK (secantRestriction W (secantDenominator W))) at hu
  have hd : fK (secantRestriction W (productX₁ W)) -
      fK (secantRestriction W (productX₂ W)) ≠ 0 := by
    simpa only [secantDenominator, map_sub] using hu.ne_zero
  rw [Affine.slope_of_X_ne (sub_ne_zero.mp hd)]
  apply (eq_div_iff hd).mpr
  simpa only [map_mul, map_sub] using congrArg fK (secantSlope_relation W)

/-- The second regular slope specializes to the field tangent-or-secant slope. -/
theorem tangentSlope_field (gK : TangentChart W →ₐ[R] K) :
    gK (tangentSlope W) = (W.map (algebraMap R K)).toAffine.slope
      (gK (tangentRestriction W (productX₁ W))) (gK (tangentRestriction W (productX₂ W)))
      (gK (tangentRestriction W (productY₁ W))) (gK (tangentRestriction W (productY₂ W))) := by
  have hu := (IsLocalization.Away.algebraMap_isUnit (tangentDenominator W)
    (S := TangentChart W)).map gK
  change IsUnit (gK (tangentRestriction W (tangentDenominator W))) at hu
  have hd : gK (tangentRestriction W (productY₁ W)) +
      gK (tangentRestriction W (productY₂ W)) + algebraMap R K W.a₁ *
      gK (tangentRestriction W (productX₂ W)) + algebraMap R K W.a₃ ≠ 0 := by
    simpa only [tangentDenominator, map_add, map_mul, AlgHom.commutes] using hu.ne_zero
  have hy : gK (tangentRestriction W (productY₁ W)) ≠
      (W.map (algebraMap R K)).toAffine.negY
        (gK (tangentRestriction W (productX₂ W)))
        (gK (tangentRestriction W (productY₂ W))) := by
    intro he
    apply hd
    simp only [Affine.negY, map_a₁, map_a₃] at he
    linear_combination he
  have ht := Affine.slope_eq_of_Y_ne _
    (productLeft_equation W (gK.comp (tangentRestriction W)))
    (productRight_equation W (gK.comp (tangentRestriction W))) hy
  simp only [AlgHom.comp_apply] at ht
  rw [ht]
  apply (eq_div_iff hd).mpr
  simpa only [map_mul, map_sub, map_add, map_pow, AlgHom.commutes,
    map_a₁, map_a₂, map_a₄] using
    congrArg gK (tangentSlope_coordinates W)

end FLT.Mazur.WeierstrassIntegralChart

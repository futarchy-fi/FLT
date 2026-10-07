/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityAdditionChart
public import FLT.Mazur.WeierstrassInfinityAdditionCompatibility
public import FLT.Mazur.WeierstrassProjectiveAdditionChart

/-!
# Equality of the normalized infinity and projective addition chart maps

After any common restriction of their domains over the Y-chart product, the
two actual algebra homomorphisms agree. Clearing the unit output coordinate
avoids any reducedness or density assumption on the common restriction.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The projective and infinity formulas have the prescribed scale in the actual slope ring. -/
theorem infinityOutputCoordinates_scaled :
    infinitySlopeRestriction W ∘ chartProductAdditionCoordinates W 1 1 =
      (infinityRight W (infinitySlopeRestriction W) 0 -
        infinityLeft W (infinitySlopeRestriction W) 0) ^ 3 • infinityOutputCoordinates W := by
  rw [chartProductAdditionCoordinates_map]
  change (W.map (algebraMap R (InfinitySlopeOpen W))).toProjective.addXYZ
    (infinityLeft W (infinitySlopeRestriction W))
    (infinityRight W (infinitySlopeRestriction W)) = _
  have hl := Projective.fin3_def (infinityLeft W (infinitySlopeRestriction W))
  have hr := Projective.fin3_def (infinityRight W (infinitySlopeRestriction W))
  rw [infinityLeft_one] at hl
  rw [infinityRight_one] at hr
  conv_lhs => rw [← hl, ← hr]
  exact infinityAdditionXYZ_scaled _ (infinityLeft_equation W _)
    (infinitySlope_mul_difference W) (infinitySlope_mul_den W)

/-- On every common restriction, the two normalized Y-chart maps coincide. -/
theorem infinityAdditionChart_compatibility
    (f : AdditionOutputOpen W 1 1 1 →ₐ[R] S) (g : InfinityAdditionOpen W →ₐ[R] S)
    (h : f.comp (additionOutputRestriction W 1 1 1) =
      g.comp (infinityAdditionRestriction W)) :
    f.comp (projectiveAdditionChart W 1 1 1) = g.comp (infinityAdditionChart W) := by
  let p := g.comp (infinityOutputRestriction W)
  let d := infinityRight W (infinitySlopeRestriction W) 0 -
    infinityLeft W (infinitySlopeRestriction W) 0
  have hs (i : Fin 3) :
      f (additionOutputRestriction W 1 1 1 (chartProductAdditionCoordinates W 1 1 i)) =
        p d ^ 3 * g (infinityOutputRestriction W (infinityOutputCoordinates W i)) := by
    have hi := congrArg p (congrFun (infinityOutputCoordinates_scaled W) i)
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow] at hi
    have hh := DFunLike.congr_fun h (chartProductAdditionCoordinates W 1 1 i)
    exact hh.trans hi
  apply projectiveAdditionChart_comp_eq
  intro i
  rw [hs i, hs 1]
  have hi := congrArg g (infinityAdditionChart_mul W i)
  simp only [map_mul] at hi
  change g (infinityAdditionChart W (coord W 1 i)) * _ = _
  linear_combination p d ^ 3 * hi

end FLT.Mazur.WeierstrassIntegralChart

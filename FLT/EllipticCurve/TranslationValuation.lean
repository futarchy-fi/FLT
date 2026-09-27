/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.PointIdealOrder
public import FLT.EllipticCurve.TranslationInfinity
/-!
# Point valuations as translated infinity valuations

Translation carries the origin to an affine point. Identifying the center
and normalization of the transported valuation identifies its local order.
-/

@[expose] public section

open Polynomial WithZero
open scoped WeierstrassCurve.Affine Polynomial.Bivariate nonZeroDivisors
namespace WeierstrassCurve.Affine.FunctionField
variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (W : Affine F) [W.IsElliptic]
omit [DecidableEq F] in
/-- A normalized valuation centered at an affine point is its adic valuation. -/
theorem pointValuation_eq_of_coordinates {u v : F} (h : W.Nonsingular u v)
    (w : Valuation W.FunctionField ℤᵐ⁰) (hw : Function.Surjective w)
    (hc : ∀ c : F, w (algebraMap F W.FunctionField c) ≤ 1)
    (hx : w (genericX W - algebraMap F W.FunctionField u) < 1)
    (hy : w (genericY W - algebraMap F W.FunctionField v) < 1) :
    (CoordinateRing.pointSpectrum h).valuation W.FunctionField = w := by
  have hx0 : w (genericX W) ≤ 1 := by
    simpa only [sub_add_cancel] using w.map_add_le hx.le (hc u)
  have hy0 : w (genericY W) ≤ 1 := by
    simpa only [sub_add_cancel] using w.map_add_le hy.le (hc v)
  have hmul {a b : ℤᵐ⁰} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := by
    calc
      a * b ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul _
  have hp (p : F[X]) : w (aeval (genericX W) p) ≤ 1 := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact w.map_add_le hp hq
    | monomial n c =>
      rw [aeval_monomial, map_mul, map_pow]
      exact hmul (hc c) (pow_le_one₀ zero_le hx0)
  have hR (a : W.CoordinateRing) : w (algebraMap W.CoordinateRing W.FunctionField a) ≤ 1 := by
    obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq a
    have he : algebraMap W.CoordinateRing W.FunctionField
        (p • 1 + q • CoordinateRing.mk W Y) =
        aeval (genericX W) p + aeval (genericX W) q * genericY W := by
      simp only [map_add, Algebra.smul_def, map_mul, mul_one, aeval_genericX]
      rfl
    rw [he]
    apply w.map_add_le (hp p)
    rw [map_mul]
    exact hmul (hp q) hy0
  let I : Ideal W.CoordinateRing :=
    { carrier := {a | w (algebraMap W.CoordinateRing W.FunctionField a) < 1}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        change w (algebraMap W.CoordinateRing W.FunctionField (a + b)) < 1
        rw [map_add]
        exact w.map_add_lt ha hb
      smul_mem' := by
        intro a b hb
        change w (algebraMap W.CoordinateRing W.FunctionField (a * b)) < 1
        rw [map_mul, map_mul]
        calc
          w (algebraMap W.CoordinateRing W.FunctionField a) *
              w (algebraMap W.CoordinateRing W.FunctionField b) ≤
              1 * w (algebraMap W.CoordinateRing W.FunctionField b) := by
            gcongr
            exact hR a
          _ < 1 := by rw [one_mul]; exact hb }
  have hI : I ≠ ⊤ := by
    intro he
    have hh : (1 : W.CoordinateRing) ∈ I := he ▸ Submodule.mem_top
    change w (algebraMap W.CoordinateRing W.FunctionField 1) < 1 at hh
    simp at hh
  have hle : CoordinateRing.XYIdeal W u (Polynomial.C v) ≤ I := by
    rw [CoordinateRing.XYIdeal, Ideal.span_le, Set.pair_subset_iff]
    constructor
    · change w (algebraMap W.CoordinateRing W.FunctionField
        (algebraMap F[X] W.CoordinateRing (X - Polynomial.C u))) < 1
      rw [← aeval_genericX, map_sub, aeval_X, aeval_C]
      exact hx
    · change w (algebraMap W.CoordinateRing W.FunctionField
        (CoordinateRing.mk W Y - algebraMap F W.CoordinateRing v)) < 1
      rw [map_sub, ← IsScalarTower.algebraMap_apply]
      exact hy
  have he := (CoordinateRing.isMaximal_XYIdeal h.1).eq_of_le hI hle
  apply (CoordinateRing.pointSpectrum h).valuation_eq_of_center w hw hR
  intro a
  change a ∈ I ↔ a ∈ CoordinateRing.XYIdeal W u (Polynomial.C v)
  rw [he]
omit [IsAlgClosed F] [DecidableEq F] [W.IsElliptic] in
/-- The parameter x/y makes the infinity valuation surjective. -/
theorem infinityValuation_surjective : Function.Surjective (infinityValuation W) := by
  intro z
  by_cases hz : z = 0
  · exact ⟨0, (map_zero _).trans hz.symm⟩
  let t := algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.XClass W 0) /
    algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.YClass W (Polynomial.C 0))
  have ht : infinityValuation W t = exp (-1 : ℤ) := infinityValuation_X_div_Y W
  refine ⟨t ^ (-log z), ?_⟩
  rw [map_zpow₀, ht, ← exp_zsmul]
  convert exp_log hz using 1
  simp
/-- Translation transports the infinity valuation to the affine point valuation. -/
theorem pointValuation_eq_translation {u v : F} (h : W.Nonsingular u v) :
    (CoordinateRing.pointSpectrum h).valuation W.FunctionField =
      (infinityValuation W).comap
        (translationPullback W (Point.some u v h)).toRingHom := by
  apply pointValuation_eq_of_coordinates W h
  · exact (infinityValuation_surjective W).comp
      (translationEquiv W (Point.some u v h)).surjective
  · intro c
    change infinityValuation W (translationPullback W _ (algebraMap F W.FunctionField c)) ≤ 1
    rw [AlgHom.commutes]
    exact Valuation.IsTrivialOn.valuation_algebraMap_le_one _ c
  · change infinityValuation W (translationPullback W _
      (genericX W - algebraMap F W.FunctionField u)) < 1
    rw [map_sub, AlgHom.commutes]
    exact (infinityValuation_translation_coordinates_sub_le W h).1.trans_lt
      (by change exp (-1 : ℤ) < exp (0 : ℤ); exact exp_lt_exp.mpr (by norm_num))
  · change infinityValuation W (translationPullback W _
      (genericY W - algebraMap F W.FunctionField v)) < 1
    rw [map_sub, AlgHom.commutes]
    exact (infinityValuation_translation_coordinates_sub_le W h).2.trans_lt
      (by change exp (-1 : ℤ) < exp (0 : ℤ); exact exp_lt_exp.mpr (by norm_num))
end WeierstrassCurve.Affine.FunctionField

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticAdditiveDepthRefinement
public import FLT.Mazur.EllipticSingularPointChart
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# Entering the deeper additive branches by an integral y-translation

After the type III and IV tests fail, any actual point outside E₀ supplies
an integral translation with coefficient depths (1,1,2,2,3). Thus the next
cubic test applies to an actual isomorphic model. No perfectness assumption
or choice of a root in an algebraic closure is needed.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

/-- Translating y by a singular point's ordinate puts the constant coefficient in I³. -/
theorem additive_translated_a6_mem_cube {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (I : Ideal R) {x y : R}
    (he : W.toAffine.Equation x y) (h1 : W.a₁ ∈ I) (h2 : W.a₂ ∈ I)
    (h4 : W.a₄ ∈ I ^ 2) (hx : x ∈ I) (hy : y ∈ I) :
    W.a₆ - y ^ 2 - W.a₃ * y ∈ I ^ 3 := by
  have hm {a b c : R} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) : a * b * c ∈ I ^ 3 := by
    simpa only [pow_succ, pow_zero, one_mul] using
      Ideal.mul_mem_mul (Ideal.mul_mem_mul ha hb) hc
  have h4x : W.a₄ * x ∈ I ^ 3 := by
    simpa only [pow_succ] using Ideal.mul_mem_mul h4 hx
  have he' := (Affine.equation_iff _ _).mp he
  have heq : W.a₆ - y ^ 2 - W.a₃ * y = W.a₁ * x * y - x ^ 3 - W.a₂ * x ^ 2 - W.a₄ * x := by
    linear_combination -he'
  rw [heq]
  exact (I ^ 3).sub_mem ((I ^ 3).sub_mem
    ((I ^ 3).sub_mem (hm h1 hx hy) (Ideal.pow_mem_pow hx 3))
    (by simpa only [pow_two, mul_assoc] using hm h2 hx hx)) h4x

/-- The failed b₆ test also deepens the translated a₃ coefficient. -/
theorem additive_translated_a3_mem_square {R : Type*} [CommRing R] [IsDomain R]
    [IsLocalRing R] (W : WeierstrassCurve R) {π x y : R}
    (hπ : π ≠ 0) (hgen : maximalIdeal R = Ideal.span {π})
    (he : W.toAffine.Equation x y) (h1 : W.a₁ ∈ maximalIdeal R)
    (h2 : W.a₂ ∈ maximalIdeal R) (h4 : W.a₄ ∈ maximalIdeal R ^ 2)
    (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R)
    (hb6 : W.b₆ ∈ maximalIdeal R ^ 3) : W.a₃ + 2 * y ∈ maximalIdeal R ^ 2 := by
  apply (square_mem_cube_iff_mem_square hπ hgen).mp
  have hc := additive_translated_a6_mem_cube W (maximalIdeal R) he h1 h2 h4 hx hy
  have hid : (W.a₃ + 2 * y) ^ 2 = W.b₆ - 4 * (W.a₆ - y ^ 2 - W.a₃ * y) := by
    rw [b₆]
    ring
  rw [hid]
  exact (maximalIdeal R ^ 3).sub_mem hb6 ((maximalIdeal R ^ 3).mul_mem_left _ hc)

/-- An actual nonsmooth point supplies the translation into depths (1,1,2,2,3). -/
theorem exists_additive_deep_y_translation {K : Type*} [Field K]
    (A : ValuationSubring K) (W : WeierstrassCurve A) {π : A} (hπ : π ≠ 0)
    (hgen : maximalIdeal A = Ideal.span {π})
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (h6 : W.a₆ ∈ maximalIdeal A ^ 2) (hb8 : W.b₈ ∈ maximalIdeal A ^ 3)
    (hb6 : W.b₆ ∈ maximalIdeal A ^ 3)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : ¬ SmoothReduction A W P) :
    ∃ t : A, t ∈ maximalIdeal A ∧
      let V := (VariableChange.mk 1 0 0 t : VariableChange A) • W
      V.a₁ ∈ maximalIdeal A ∧ V.a₂ ∈ maximalIdeal A ∧
      V.a₃ ∈ maximalIdeal A ^ 2 ∧ V.a₄ ∈ maximalIdeal A ^ 2 ∧
      V.a₆ ∈ maximalIdeal A ^ 3 := by
  have h4' := (b8_mem_cube_iff_a4_mem_square W hπ hgen h1 h2 h3 h4 h6).mp hb8
  obtain ⟨x, y, hn, hx, hy, _⟩ := exists_singular_integral_affine A W h3 h4
    (Ideal.pow_le_self (by decide : 2 ≠ 0) h6) P hP
  have he := (W.toAffine.map_equation (IsFractionRing.injective A K) x y).mp hn.1
  have h3' := additive_translated_a3_mem_square W hπ hgen he h1 h2 h4' hx hy hb6
  have h6' := additive_translated_a6_mem_cube W (maximalIdeal A) he h1 h2 h4' hx hy
  have h4'' : W.a₄ - y * W.a₁ ∈ maximalIdeal A ^ 2 := by
    exact (maximalIdeal A ^ 2).sub_mem h4' (by simpa only [pow_two] using Ideal.mul_mem_mul hy h1)
  rw [sub_right_comm] at h6'
  refine ⟨y, hy, ?_⟩
  dsimp
  simpa only [variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_one, inv_one, one_pow, one_mul,
    zero_mul, mul_zero, zero_add, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), mul_comm y W.a₃] using ⟨h1, h2, h3', h4'', h6'⟩

end FLT.Mazur

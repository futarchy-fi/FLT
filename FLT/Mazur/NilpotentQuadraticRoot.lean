/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.Tactic.LinearCombination

/-!
# The unique small root of a quadratic over a nilpotent thickening

A nilpotent ideal is already complete. Hensel lifting therefore constructs,
rather than assumes, the root reducing to zero when the linear coefficient
is a unit. Uniqueness makes these roots compatible with coefficient maps.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NilpotentQuadraticRoot
open Polynomial Submodule
variable {R : Type*} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)

include hI in
/-- A nilpotent ideal gives a complete adic topology without a Noetherian hypothesis. -/
theorem complete : IsAdicComplete I R := by
  obtain ⟨N, hN⟩ := hI
  have hN' : I ^ N = ⊥ := hN
  let _ : IsHausdorff I R := ⟨fun x hx ↦ by
    simpa only [hN', bot_smul, SModEq.bot] using hx N⟩
  let _ : IsPrecomplete I R := ⟨fun f hf ↦ by
    refine ⟨f N, fun n ↦ ?_⟩
    obtain hn | hn := le_total n N
    · exact hf hn
    · have he := hf hn
      simp only [hN', bot_smul, SModEq.bot] at he
      rw [he]⟩
  exact ⟨⟩

include hI in
/-- Every element of the nilpotent ideal is nilpotent in the ring. -/
theorem element_nilpotent {x : R} (hx : x ∈ I) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := hI
  refine ⟨N, ?_⟩
  have hm := Ideal.pow_mem_pow hx N
  rw [hN] at hm
  exact hm

variable (a b : R) (ha : IsUnit a) (hb : b ∈ I)

/-- The coefficient polynomial is monic over any commutative ring. -/
theorem quadratic_monic : (X ^ 2 + C a * X - C b : R[X]).Monic := by
  have he : (X ^ 2 + C a * X - C b : R[X]) = Cubic.toPoly ⟨0, 1, a, -b⟩ := by
    simp only [Cubic.toPoly, C_0, C_1, C_neg, zero_mul, one_mul, zero_add]
    ring
  rw [he]
  exact Cubic.monic_of_b_eq_one'

include hI ha hb in
/-- Hensel lifting supplies an actual root in the original nilpotent ideal. -/
theorem exists_root : ∃ x : R, x ∈ I ∧ x ^ 2 + a * x = b := by
  let _ := complete I hI
  obtain ⟨x, hx, hi⟩ := HenselianRing.is_henselian
    (I := I) (X ^ 2 + C a * X - C b) (quadratic_monic a b) 0
    (by simpa using I.neg_mem hb)
    (by simpa using ha.map (Ideal.Quotient.mk I))
  refine ⟨x, by simpa using hi, ?_⟩
  simpa only [IsRoot, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C,
    sub_eq_zero] using hx

include hI ha in
/-- The root in the nilpotent ideal is unique; no choice of a second branch is hidden. -/
theorem root_unique {x y : R} (hx : x ∈ I) (hy : y ∈ I)
    (hex : x ^ 2 + a * x = b) (hey : y ^ 2 + a * y = b) : x = y := by
  have hu : IsUnit (x + y + a) :=
    (element_nilpotent I hI (I.add_mem hx hy)).isUnit_add_right_of_commute ha (mul_comm _ _)
  have hz : (x - y) * (x + y + a) = 0 := by linear_combination hex - hey
  exact sub_eq_zero.mp ((hu.mul_left_eq_zero).mp hz)

/-- The selected root is constructed from the coefficients, not an input branch. -/
def root : R := (exists_root I hI a b ha hb).choose

/-- The constructed branch reduces to zero. -/
theorem root_mem : root I hI a b ha hb ∈ I := (exists_root I hI a b ha hb).choose_spec.1

/-- The constructed branch satisfies its original equation. -/
theorem root_equation : root I hI a b ha hb ^ 2 + a * root I hI a b ha hb = b :=
  (exists_root I hI a b ha hb).choose_spec.2

end FLT.Mazur.NilpotentQuadraticRoot

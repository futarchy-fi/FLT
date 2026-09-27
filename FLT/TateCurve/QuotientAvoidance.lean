/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.LocalField
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Avoiding finite sets of Tate parameters

The multiplicative quotient has infinitely many classes, but every square
fiber is finite. These facts supply auxiliary parameters for addition.
-/

@[expose] public section

open ValuativeRel

namespace TateCurve

section Algebra

variable {K : Type*} [Field K]

/-- A square equation has finitely many solutions in a field. -/
private theorem finite_square_roots (a : K) : {u : K | u ^ 2 = a}.Finite := by
  have hn : (Polynomial.X ^ 2 - Polynomial.C a : Polynomial K) ≠ 0 := by
    intro h
    have hc := congrArg (Polynomial.coeff · 2) h
    simp at hc
  simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using Polynomial.finite_setOfPred_isRoot hn

/-- A square equation in the quotient by a cyclic subgroup has finitely many solutions. -/
theorem finite_quotient_square_fiber (q : Kˣ) (a : Kˣ ⧸ Subgroup.zpowers q) :
    {b : Kˣ ⧸ Subgroup.zpowers q | b ^ 2 = a}.Finite := by
  classical
  induction a using Quotient.inductionOn with
  | h v =>
    let S (r : Fin 2) : Set Kˣ := {w | (w : K) ^ 2 = (v : K) * (q : K) ^ (r : ℕ)}
    have hS (r : Fin 2) : (S r).Finite :=
      (finite_square_roots ((v : K) * (q : K) ^ (r : ℕ))).preimage Units.val_injective.injOn
    apply ((Set.finite_iUnion hS).image
      (QuotientGroup.mk : Kˣ → Kˣ ⧸ Subgroup.zpowers q)).subset
    intro b hb
    induction b using Quotient.inductionOn with
    | h u =>
      change (u : Kˣ ⧸ Subgroup.zpowers q) ^ 2 = v at hb
      have hm : u ^ 2 / v ∈ Subgroup.zpowers q := by
        apply QuotientGroup.eq_iff_div_mem.mp
        simpa only [QuotientGroup.mk_pow] using hb
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hm
      have hu : u ^ 2 = q ^ m * v := by
        simpa only [div_mul_cancel] using congrArg (· * v) hm.symm
      let r : Fin 2 := ⟨(m % 2).toNat, by omega⟩
      let w : Kˣ := q ^ (-(m / 2)) * u
      have hw : w ^ 2 = v * q ^ (r : ℕ) := by
        dsimp only [w]
        rw [mul_pow, ← zpow_natCast, ← zpow_mul, hu]
        rw [← mul_assoc, ← zpow_add]
        have he : -(m / 2) * (2 : ℤ) + m = (r : ℕ) := by dsimp [r]; omega
        norm_num only [Nat.cast_ofNat]
        rw [he, zpow_natCast, mul_comm]
      refine ⟨w, Set.mem_iUnion.mpr ⟨r, ?_⟩, ?_⟩
      · exact congrArg Units.val hw
      · change ((q ^ (-(m / 2)) * u : Kˣ) : Kˣ ⧸ Subgroup.zpowers q) = u
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow,
          (QuotientGroup.eq_one_iff q).mpr (Subgroup.mem_zpowers q), one_zpow, one_mul]

end Algebra

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A power of the Tate parameter of valuation one has exponent zero. -/
theorem zpow_eq_one_of_valuation_eq_one (q : Kˣ) (hq : valuation K (q : K) < 1)
    {m : ℤ} (hm : valuation K ((q ^ m : Kˣ) : K) = 1) : m = 0 := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀] at hm
  exact (zpow_eq_one_iff_right₀ zero_le hq.ne).mp hm

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Two units of valuation one have the same quotient class only when they are equal. -/
theorem quotient_mk_injective_on_valuation_one (q : Kˣ)
    (hq : valuation K (q : K) < 1) {u v : Kˣ}
    (hu : valuation K (u : K) = 1) (hv : valuation K (v : K) = 1)
    (h : (u : Kˣ ⧸ Subgroup.zpowers q) = v) : u = v := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.eq_iff_div_mem.mp h)
  have hval : valuation K ((q ^ m : Kˣ) : K) = 1 := by
    rw [hm]
    simp [hu, hv]
  have hm0 := zpow_eq_one_of_valuation_eq_one q hq hval
  rw [hm0, zpow_zero] at hm
  exact div_eq_one.mp hm.symm

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The quotient by the Tate parameter has infinitely many elements. -/
theorem infinite_quotient (q : Kˣ) (hq : valuation K (q : K) < 1) :
    Infinite (Kˣ ⧸ Subgroup.zpowers q) := by
  have hval (n : ℕ) : valuation K (1 + (q : K) ^ (n + 1)) = 1 :=
    (valuation K).map_one_add_of_lt
      (by rw [map_pow]; exact pow_lt_one₀ zero_le hq (Nat.succ_ne_zero n))
  have hn (n : ℕ) : 1 + (q : K) ^ (n + 1) ≠ 0 := by
    intro h
    have he := hval n
    simp [h] at he
  let f (n : ℕ) : Kˣ ⧸ Subgroup.zpowers q := ↑(Units.mk0 _ (hn n))
  apply Infinite.of_injective f
  intro a b h
  have he := quotient_mk_injective_on_valuation_one q hq (hval a) (hval b) h
  have hp : (q : K) ^ (a + 1) = (q : K) ^ (b + 1) :=
    add_left_cancel (congrArg Units.val he)
  have hpv := congrArg (valuation K) hp
  rw [map_pow, map_pow] at hpv
  have hi := pow_right_injective₀ (zero_lt_iff.mpr ((valuation K).ne_zero_iff.mpr q.ne_zero))
    hq.ne hpv
  omega

end TateCurve

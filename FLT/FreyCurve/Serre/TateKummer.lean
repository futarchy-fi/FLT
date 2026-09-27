/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.TateTorsion

/-!
# Normalized Kummer representatives of Tate torsion

The exponent of a torsion representative can be chosen in `[0,n)`.
These representatives give the geometric points of the Kummer model.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
open ValuativeRel

namespace WeierstrassCurve

variable {K Ω : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (E : WeierstrassCurve K) [E.IsElliptic] [E.HasSplitMultiplicativeReduction 𝒪[K]]
  [Field Ω] [Algebra K Ω] [DecidableEq Ω] [Algebra.IsAlgebraic K Ω]

/-- Every Tate torsion point has a representative with exponent between zero and `n - 1`. -/
theorem exists_normalized_tate_torsion_rep {n : ℕ} (hn : 0 < n)
    (P : AddSubgroup.torsionBy (E⁄Ω).Point (n : ℤ)) :
    ∃ (i : Fin n) (x : Ωˣ), E.tatePoint Ω x = P ∧
      x ^ n = E.qUnitSepClosure Ω ^ i.val := by
  obtain ⟨x, m, hx, hm⟩ := E.exists_tatePoint_torsionBy_rep Ω n P
  let q := E.qUnitSepClosure Ω
  have hr0 := Int.emod_nonneg m (show (n : ℤ) ≠ 0 by omega)
  have hrlt := Int.emod_lt_of_pos m (show (0 : ℤ) < n by omega)
  let i : Fin n := ⟨(m % (n : ℤ)).toNat, by omega⟩
  have hi : (i.val : ℤ) = m % (n : ℤ) := by
    dsimp [i]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have he : m - (m / (n : ℤ)) * n = (i.val : ℤ) := by
    rw [hi, Int.emod_def, mul_comm (n : ℤ)]
  refine ⟨i, x / q ^ (m / (n : ℤ)), ?_, ?_⟩
  · have hz : E.tatePoint Ω (q ^ (m / (n : ℤ))) = 0 :=
      (E.tatePoint_eq_zero_iff Ω _).mpr (Subgroup.zpow_mem_zpowers _ _)
    have h := E.tatePoint_mul Ω (x / q ^ (m / (n : ℤ))) (q ^ (m / (n : ℤ)))
    simpa only [div_mul_cancel, hz, add_zero, hx] using h.symm
  · dsimp only [q]
    rw [div_pow, hm, ← zpow_natCast, ← zpow_mul, div_eq_mul_inv,
      ← zpow_sub, he, zpow_natCast]

/-- Two normalized Tate torsion representatives giving the same point are equal. -/
theorem normalized_tate_torsion_rep_injective {n : ℕ} (hn : 0 < n)
    {i j : Fin n} {x y : Ωˣ}
    (hx : x ^ n = E.qUnitSepClosure Ω ^ i.val)
    (hy : y ^ n = E.qUnitSepClosure Ω ^ j.val)
    (hxy : E.tatePoint Ω x = E.tatePoint Ω y) : i = j ∧ x = y := by
  have hij := E.tatePoint_exponent_eq Ω (n := n) (a := i.val) (b := j.val)
    (by simpa only [zpow_natCast] using hx)
    (by simpa only [zpow_natCast] using hy) hxy
  have hi : i = j := by
    apply Fin.ext
    have hcast : (i.val : ZMod n) = (j.val : ZMod n) := by
      simpa only [Int.cast_natCast] using hij
    simpa only [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt i.isLt,
      Nat.mod_eq_of_lt j.isLt] using hcast
  subst j
  refine ⟨rfl, ?_⟩
  have hquot : (x : Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) = y :=
    (E.tateEquivSepClosure Ω).injective hxy
  obtain ⟨c, hc⟩ := QuotientGroup.eq_iff_div_mem.mp hquot
  dsimp only at hc
  have hc0 : c * (n : ℤ) = 0 := by
    apply (injective_zpow_iff_not_isOfFinOrder.mpr
      (E.qUnitSepClosure_not_isOfFinOrder Ω))
    change E.qUnitSepClosure Ω ^ (c * (n : ℤ)) = E.qUnitSepClosure Ω ^ (0 : ℤ)
    rw [zpow_mul, zpow_natCast, hc, div_pow, hx, hy]
    simp
  have hc' : c = 0 := (mul_eq_zero.mp hc0).resolve_right (by omega)
  rw [hc', zpow_zero] at hc
  exact div_eq_one.mp hc.symm

end WeierstrassCurve

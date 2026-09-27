/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.Abscissa
public import FLT.TateCurve.Points
public import FLT.TateCurve.Quotient

/-!
# Fibers of the Tate abscissa

Normalizing representatives to the fundamental annulus combines the interior
and boundary estimates. Every nonidentity abscissa fiber consists of at most
one pair of inverse quotient classes.
-/

@[expose] public section

open ValuativeRel

namespace TateCurve

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Equal nonidentity Tate abscissae identify equal or inverse quotient classes. -/
theorem tateX_eq_iff_quotient (q u v : Kˣ) (hq : valuation K (q : K) < 1)
    (hu : u ∉ Subgroup.zpowers q) (hv : v ∉ Subgroup.zpowers q) :
    tateX (u : K) (q : K) = tateX (v : K) (q : K) ↔
      (u : Kˣ ⧸ Subgroup.zpowers q) = v ∨
        (u : Kˣ ⧸ Subgroup.zpowers q) = (v : Kˣ ⧸ Subgroup.zpowers q)⁻¹ := by
  constructor
  · intro h
    obtain ⟨m, hUm, hUle⟩ := exists_zpow_mul_mem_annulus q u hq
    obtain ⟨n, hVn, hVle⟩ := exists_zpow_mul_mem_annulus q v hq
    let U : Kˣ := q ^ m * u
    let V : Kˣ := q ^ n * v
    have hUm : valuation K (q : K) < valuation K (U : K) := by
      simpa only [U, Units.val_mul, Units.val_zpow_eq_zpow_val] using hUm
    have hVn : valuation K (q : K) < valuation K (V : K) := by
      simpa only [V, Units.val_mul, Units.val_zpow_eq_zpow_val] using hVn
    have hUle : valuation K (U : K) ≤ 1 := by
      simpa only [U, Units.val_mul, Units.val_zpow_eq_zpow_val] using hUle
    have hVle : valuation K (V : K) ≤ 1 := by
      simpa only [V, Units.val_mul, Units.val_zpow_eq_zpow_val] using hVle
    have hmk (a : Kˣ) (r : ℤ) :
        (↑(q ^ r * a) : Kˣ ⧸ Subgroup.zpowers q) = a := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow,
        (QuotientGroup.eq_one_iff q).mpr (Subgroup.mem_zpowers q), one_zpow, one_mul]
    have hU : (U : Kˣ ⧸ Subgroup.zpowers q) = u := hmk u m
    have hV : (V : Kˣ ⧸ Subgroup.zpowers q) = v := hmk v n
    have hU1 : (U : K) ≠ 1 := by
      intro h1
      apply hu
      apply (QuotientGroup.eq_one_iff u).mp
      rw [← hU, show U = 1 from Units.ext h1]
      rfl
    have hV1 : (V : K) ≠ 1 := by
      intro h1
      apply hv
      apply (QuotientGroup.eq_one_iff v).mp
      rw [← hV, show V = 1 from Units.ext h1]
      rfl
    have hEq : tateX (U : K) (q : K) = tateX (V : K) (q : K) := by
      simpa only [U, V, Units.val_mul, Units.val_zpow_eq_zpow_val,
        tateX_zpow_mul _ q.ne_zero] using h
    have hqU : valuation K ((q : K) / U) < 1 := by
      rw [map_div₀]
      exact (div_lt_one₀ (zero_lt_iff.mpr ((valuation K).ne_zero_iff.mpr U.ne_zero))).mpr hUm
    have hqV : valuation K ((q : K) / V) < 1 := by
      rw [map_div₀]
      exact (div_lt_one₀ (zero_lt_iff.mpr ((valuation K).ne_zero_iff.mpr V.ne_zero))).mpr hVn
    have hcases : U = V ∨ U * V = 1 ∨ U * V = q := by
      rcases hUle.eq_or_lt with hUeq | hUlt
      · rcases hVle.eq_or_lt with hVeq | hVlt
        · rcases (tateX_eq_iff_of_valuation_eq_one q.ne_zero U.ne_zero V.ne_zero
            hU1 hV1 hq hUeq hVeq).mp hEq with he | he
          · exact Or.inl (Units.ext he)
          · exact Or.inr (Or.inl (Units.ext he))
        · have ha := one_le_valuation_tateX_of_valuation_eq_one q.ne_zero U.ne_zero hU1 hq hUeq
          have hb := valuation_tateX_lt_one_of_open_annulus q.ne_zero V.ne_zero hq hVlt hqV
          rw [hEq] at ha
          exact False.elim (not_lt_of_ge ha hb)
      · rcases hVle.eq_or_lt with hVeq | hVlt
        · have ha := one_le_valuation_tateX_of_valuation_eq_one q.ne_zero V.ne_zero hV1 hq hVeq
          have hb := valuation_tateX_lt_one_of_open_annulus q.ne_zero U.ne_zero hq hUlt hqU
          rw [hEq] at hb
          exact False.elim (not_lt_of_ge ha hb)
        · rcases (tateX_eq_iff_of_open_annulus q.ne_zero U.ne_zero V.ne_zero hq
            hUlt hqU hVlt hqV).mp hEq with he | he
          · exact Or.inl (Units.ext he)
          · exact Or.inr (Or.inr (Units.ext he))
    rcases hcases with he | he | he
    · exact Or.inl (hU.symm.trans ((congrArg (QuotientGroup.mk) he).trans hV))
    · apply Or.inr
      apply eq_inv_of_mul_eq_one_left
      rw [← hU, ← hV, ← QuotientGroup.mk_mul, he]
      rfl
    · apply Or.inr
      apply eq_inv_of_mul_eq_one_left
      rw [← hU, ← hV, ← QuotientGroup.mk_mul, he]
      exact (QuotientGroup.eq_one_iff q).mpr (Subgroup.mem_zpowers q)
  · rintro (h | h)
    · exact congrArg (fun a ↦ (quotientCoordinates q a).1) h
    · have he := congrArg (fun a ↦ (quotientCoordinates q a).1) h
      change tateX (u : K) (q : K) = tateX ((v⁻¹ : Kˣ) : K) (q : K) at he
      simpa only [Units.val_inv_eq_inv_val, tateX_inv q.ne_zero v.ne_zero] using he

end TateCurve

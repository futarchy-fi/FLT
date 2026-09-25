/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# Prime-to-residue-characteristic roots of unity

Reduction is injective on roots of unity whose order is invertible in the local
ring. Consequently inertia fixes these roots of unity in a valued extension.
-/

@[expose] public section

open Polynomial

/-- Reduction in a local ring separates roots of unity of invertible order. -/
theorem IsLocalRing.eq_of_pow_eq_one_of_residue_eq {R : Type*} [CommRing R]
    [IsLocalRing R] {n : ℕ} (hn : IsUnit (n : R)) {x y : R}
    (hx : x ^ n = 1) (hy : y ^ n = 1)
    (hxy : IsLocalRing.residue R x = IsLocalRing.residue R y) : x = y := by
  by_cases hn0 : n = 0
  · subst n
    simp at hn
  have hxunit : IsUnit x := IsUnit.of_pow_eq_one hx hn0
  apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub (f := X ^ n - 1)
  · simpa using sub_eq_zero.mpr hx
  · simpa using sub_eq_zero.mpr hy
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simp [map_sub, hxy]
  · simpa [derivative_X_pow] using hn.mul (hxunit.pow (n - 1))

/-- Inertia fixes roots of unity whose order is invertible in the valuation ring. -/
theorem ValuationSubring.inertia_fixes_of_pow_eq_one
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) {n : ℕ} (hn : IsUnit (n : A))
    (σ : A.decompositionSubgroup K) (hσ : σ ∈ A.inertiaSubgroup K)
    {x : L} (hx : x ^ n = 1) : (σ : L ≃ₐ[K] L) x = x := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hxmem : x ∈ A := by
    apply A.mem_of_valuation_le_one
    apply (pow_le_one_iff hn0).mp
    rw [← map_pow, hx, map_one]
  let y : A := ⟨x, hxmem⟩
  have hy : y ^ n = 1 := Subtype.ext hx
  have hres : σ • IsLocalRing.residue A y = IsLocalRing.residue A y :=
    congrArg (fun f : RingAut (IsLocalRing.ResidueField A) ↦
      f (IsLocalRing.residue A y)) hσ
  have heq : σ • y = y := IsLocalRing.eq_of_pow_eq_one_of_residue_eq hn
    (by rw [← smul_pow', hy, smul_one]) hy
    (by rw [IsLocalRing.ResidueField.residue_smul, hres])
  exact congrArg Subtype.val heq

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.KrullDimension.Regular

/-! # Length bounds for regular sequences in local rings -/

@[expose] public section

namespace RingTheory.Sequence

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The length of a regular sequence is bounded by the local ring's dimension. -/
theorem IsRegular.length_le_ringKrullDim {rs : List R} (h : IsRegular R rs) :
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim R := by
  have : Nontrivial (R ⧸ Ideal.ofList rs) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using h.top_ne_smul.symm
  calc
    (rs.length : WithBot ℕ∞) = 0 + rs.length := (zero_add _).symm
    _ ≤ ringKrullDim (R ⧸ Ideal.ofList rs) + rs.length :=
      add_le_add (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ Ideal.ofList rs)) le_rfl
    _ = ringKrullDim R := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs h

/-- Once a full-length regular sequence is known, no longer sequence can exist. -/
theorem IsRegular.length_le_of_ringKrullDim_eq {rs : List R} (h : IsRegular R rs)
    {n : ℕ} (hdim : ringKrullDim R = n) : rs.length ≤ n := by
  have hle := h.length_le_ringKrullDim
  rw [hdim] at hle
  exact_mod_cast hle

end RingTheory.Sequence

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Odlyzko

/-!
# The auxiliary degree bound for the three-adic argument

The explicit discriminant bound and divisibility by six reduce the degree to six or twelve.
-/

@[expose] public section

/-- The Odlyzko bound restricts an auxiliary field with the given discriminant bound
and degree divisible by six to degree six or twelve. -/
theorem auxiliary_degree_eq_six_or_twelve
    (L : Type*) [Field L] [NumberField L] [NumberField.IsTotallyComplex L]
    (h6 : 6 ∣ Module.finrank ℚ L)
    (hdisc : |(NumberField.discr L : ℝ)| ≤
      ((2 : ℝ) ^ (2 / 3 : ℝ) * (3 : ℝ) ^ (3 / 2 : ℝ)) ^ Module.finrank ℚ L) :
    Module.finrank ℚ L = 6 ∨ Module.finrank ℚ L = 12 := by
  have hlt : Module.finrank ℚ L < 18 := by
    by_contra h
    exact Odlyzko.not_discriminant_le_fontaine_bound L (by omega) hdisc
  have hpos := Module.finrank_pos (R := ℚ) (M := L)
  obtain ⟨n, hn⟩ := h6
  omega

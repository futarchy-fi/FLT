/-
Copyright (c) 2026 Kelly Azevedo Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelly Azevedo Santos
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# The Odlyzko endgame interface

This file freezes the target of the Odlyzko endgame before its analytic proof is assembled.
The existing axiom in `FLT.Assumptions.Odlyzko` remains untouched until that assembly is
complete.
-/

@[expose] public section

open Polynomial NumberField Module

namespace Odlyzko

universe u

/-- The final M11 conclusion, in exactly the form required by the existing Odlyzko axiom. -/
theorem Odlyzko_statement (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hdim : finrank ℚ K ≥ 18) : |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K := by
  sorry

/-- Assemble the frozen Odlyzko statement from the M11 conclusion supplied as a hypothesis. -/
theorem odlyzko_statement_of_m11
    (hM11 : ∀ (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K],
      finrank ℚ K ≥ 18 → |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K)
    (K : Type u) [Field K] [NumberField K] [IsTotallyComplex K]
    (hdim : finrank ℚ K ≥ 18) : |(discr K : ℝ)| ≥ 8.25 ^ finrank ℚ K :=
  hM11 K hdim

/-- Contradiction form of the Odlyzko bound for the hardly-ramified mod-three consumer. -/
theorem not_discriminant_le_fontaine_bound
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (hdim : finrank ℚ K ≥ 18)
    (hdisc : |(discr K : ℝ)| ≤
      (((2 : ℝ) ^ (2 / 3 : ℝ)) * (3 : ℝ) ^ (3 / 2 : ℝ)) ^ finrank ℚ K) : False := by
  sorry

end Odlyzko

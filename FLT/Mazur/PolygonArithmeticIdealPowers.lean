/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageCoefficients
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Original ideal powers in the arithmetic quotients

Every arithmetic power is the image of its original ideal power. Below
the truncation order, membership is reflected back to the original coefficient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonArithmeticStages
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => algebraMap R Q
local notation "J" => ideal Q (parameter R π m)

/-- Each power of the quotient parameter ideal is the image of the original ideal power. -/
theorem parameterIdeal_pow_eq_map (n : ℕ) :
    J ^ n = (ideal R π ^ n).map q := by
  rw [Ideal.map_pow]
  congr 1
  change Ideal.span {q π} = (Ideal.span {π}).map q
  rw [Ideal.map_span, Set.image_singleton]

/-- Original ideal membership survives at every arithmetic quotient order. -/
theorem coefficient_mem_parameterIdeal_pow (n : ℕ) {c : R} (hc : c ∈ ideal R π ^ n) :
    q c ∈ J ^ n := by
  rw [parameterIdeal_pow_eq_map]
  exact Ideal.mem_map_of_mem q hc

/-- Below the truncation order the actual quotient detects the original ideal depth. -/
theorem coefficient_mem_parameterIdeal_pow_iff (n : ℕ) (hn : n ≤ m + 1) (c : R) :
    q c ∈ J ^ n ↔ c ∈ ideal R π ^ n := by
  rw [parameterIdeal_pow_eq_map]
  change c ∈ Ideal.comap (Ideal.Quotient.mk (ideal R π ^ (m + 1)))
    ((ideal R π ^ n).map (Ideal.Quotient.mk (ideal R π ^ (m + 1)))) ↔ _
  rw [Ideal.comap_map_mk (Ideal.pow_le_pow_right hn)]

/-- Exact original coefficient depth is retained whenever the quotient sees its next order. -/
theorem coefficient_exact_parameterIdeal_depth (n : ℕ) (hn : n ≤ m) {c : R}
    (hc : c ∈ ideal R π ^ n) (hc' : c ∉ ideal R π ^ (n + 1)) :
    q c ∈ J ^ n ∧ q c ∉ J ^ (n + 1) := by
  refine ⟨coefficient_mem_parameterIdeal_pow π m n hc, ?_⟩
  intro h
  exact hc' ((coefficient_mem_parameterIdeal_pow_iff π m (n + 1) (by omega) c).mp h)

end FLT.Mazur.PolygonArithmeticStages

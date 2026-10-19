/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Regular roots with unit leading coefficient

A polynomial equation in a fraction field with unit leading coefficient
forces its root into the original integrally closed ring. The polynomial
need not be monic, and the equation is in the full fraction field.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.IntegralPolynomialRootRegularity
variable {R K : Type*} [CommRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] [IsIntegrallyClosed R]

/-- A unit leading coefficient lets an integral multiple recover the original root. -/
theorem root_mem_range (p : Polynomial R) (x : K)
    (hp : p.eval₂ (algebraMap R K) x = 0) (hu : IsUnit p.leadingCoeff) :
    x ∈ (algebraMap R K).range := by
  obtain ⟨u, hu⟩ := hu
  have hi := (algebraMap R K).isIntegralElem_leadingCoeff_mul p x hp
  change IsIntegral R (algebraMap R K p.leadingCoeff * x) at hi
  rw [← hu] at hi
  have hx := (isIntegral_algebraMap (R := R) (A := K) (x := (↑u⁻¹ : R))).mul hi
  have he : algebraMap R K (↑u⁻¹ : R) * (algebraMap R K (↑u : R) * x) = x := by
    rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [he] at hx
  exact IsIntegrallyClosed.isIntegral_iff.mp hx

end FLT.Mazur.IntegralPolynomialRootRegularity

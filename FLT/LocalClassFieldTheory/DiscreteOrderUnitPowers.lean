/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedOrderMap

/-!
# Unit representatives modulo powers over a DVR

Divisibility of integer order is exactly the existence of an integral-unit
representative after dividing by a power. This statement uses no Galois data.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

variable (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Integer-order divisibility detects independent unit representatives modulo powers. -/
theorem discreteOrder_dvd_iff_unit_power (n : ℕ) (a : Kˣ) :
    (n : ℤ) ∣ discreteOrderAdd R K (Additive.ofMul a) ↔
      ∃ (b : Kˣ) (u : Rˣ), a = b ^ n * Units.map (algebraMap R K) u := by
  change (n : ℤ) ∣ (discreteOrder R K a).toAdd ↔ _
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨b, hb⟩ := discreteOrder_surjective R K (Multiplicative.ofAdd j)
    have hz : discreteOrder R K (a / b ^ n) = 1 := by
      apply Multiplicative.toAdd.injective
      simp only [map_div, map_pow, hb, toAdd_div, toAdd_pow, toAdd_ofAdd, toAdd_one,
        nsmul_eq_mul, hj, sub_self]
    obtain ⟨u, hu⟩ := (discreteOrder_eq_one_iff R K _).mp hz
    refine ⟨b, u, ?_⟩
    rw [hu, mul_div_cancel]
  · rintro ⟨b, u, rfl⟩
    rw [map_mul, map_pow, discreteOrder_unit, mul_one, toAdd_pow, nsmul_eq_mul]
    exact dvd_mul_right _ _

end LocalClassFieldTheory

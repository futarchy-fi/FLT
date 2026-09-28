/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Rational primes and absolute ramification indices

The arithmetic point-field API uses the ring of integers of `ℚ`, whereas
explicit Kummer computations use `ℤ`. These lemmas identify the corresponding
lying-over conditions and ramification indices.
-/

@[expose] public noncomputable section

open NumberField

namespace ThreeAdicPlan

/-- A prime above the integer `p` also lies above the associated rational place. -/
theorem liesOver_ratPrime_of_liesOver_int {L : Type*} [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) {p : ℕ} (hp : p.Prime)
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.LiesOver hp.toHeightOneSpectrumRingOfIntegersRat.asIdeal := by
  rw [Ideal.liesOver_iff]
  change Ideal.comap Rat.ringOfIntegersEquiv.toRingHom (Ideal.span {(p : ℤ)}) = _
  rw [Ideal.over_def P (Ideal.span {(p : ℤ)})]
  ext x
  simp only [Ideal.mem_comap, Ideal.under_def]
  obtain ⟨z, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
  simp [eq_intCast]

/-- Absolute ramification is unchanged by identifying the integers of `ℚ` with `ℤ`. -/
theorem ramificationIdx_int_eq_ratIntegers {L : Type*} [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.IsPrime] :
    P.ramificationIdx ℤ = P.ramificationIdx (𝓞 ℚ) := by
  have : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
    Algebra.FormallyUnramified.of_equiv Rat.ringOfIntegersEquiv.symm.toIntAlgEquiv
  rw [Ideal.ramificationIdx_tower (R := ℤ) (P.under (𝓞 ℚ)) P,
    Ideal.ramificationIdx_eq_one, one_mul]

end ThreeAdicPlan

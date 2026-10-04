/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.WittCoefficientRing
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Faithful Witt coefficients and characteristic zero

For an algebra over the constructed unramified coefficient ring, surviving
powers of p are exactly faithfulness of the coefficient map and characteristic
zero. No reducedness or domain assumption on the target is needed.
-/

@[expose] public noncomputable section
namespace Deformation.WittCoefficients
variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [Finite k]
  (A : Type*) [CommRing A] [Algebra (WittVector p k) A]

/-- A nonzero coefficient is a unit times a power of p, so killing it kills such a power. -/
theorem algebraMap_injective_iff :
    Function.Injective (algebraMap (WittVector p k) A) ↔ ¬ IsNilpotent (p : A) := by
  constructor
  · intro hinj ⟨n, hn⟩
    apply p_pow_ne_zero p k n
    apply hinj
    simpa only [map_pow, map_natCast, map_zero] using hn
  · intro h
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    by_contra hx0
    obtain ⟨n, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' x hx0
    rw [map_mul, map_pow, map_natCast] at hx
    have hu := u.isUnit.map (algebraMap (WittVector p k) A)
    exact h ⟨n, (hu.mul_left_eq_zero).mp hx⟩

include k in
/-- Nonnilpotence already gives characteristic zero on the entire algebra, before taking a prime. -/
theorem charZero_of_p_nonnilpotent (h : ¬ IsNilpotent (p : A)) : CharZero A :=
  charZero_of_injective_algebraMap ((algebraMap_injective_iff p k A).mpr h)

include k in
/-- The coefficient nonvanishing assertion is equivalent to characteristic zero. -/
theorem charZero_iff : CharZero A ↔ ¬ IsNilpotent (p : A) := by
  constructor
  · intro hc
    let := hc
    rintro ⟨n, hn⟩
    have hp : p ^ n ≠ 0 := pow_ne_zero n (Fact.out : p.Prime).ne_zero
    exact hp (Nat.cast_eq_zero.mp (by simpa only [Nat.cast_pow] using hn :
      ((p ^ n : ℕ) : A) = 0))
  · exact charZero_of_p_nonnilpotent p k A

include k in
/-- For a prime quotient, avoiding p suffices for faithful coefficients. -/
theorem primeQuotient_charZero (P : Ideal A) [P.IsPrime] (hp : (p : A) ∉ P) :
    CharZero (A ⧸ P) := by
  apply charZero_of_p_nonnilpotent p k
  rintro ⟨n, hn⟩
  have hp0 : (p : A ⧸ P) ≠ 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P)]
    exact fun h ↦ hp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  exact (pow_ne_zero n hp0) hn

end Deformation.WittCoefficients

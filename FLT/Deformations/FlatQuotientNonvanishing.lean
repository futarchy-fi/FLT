/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.FlatClosedQuotient
public import FLT.GaloisRepresentation.HardlyRamified.LiftPrimeAvoidingP

/-!
# The nonvanishing gate after imposing finite flatness

Residual properness does not prove that powers of p survive. This module
identifies the exact remaining nonnilpotence condition on the constructed
ideal, and proves that every characteristic-zero specialization requires it.
-/

@[expose] public noncomputable section
open NumberField
namespace Deformation
open ProartinianCat
variable {O : Type} [CommRing O] [IsLocalRing O]
  [Finite (IsLocalRing.ResidueField O)] (U : ProartinianCat O)
  {K : Type} [Field K] [NumberField K] {n : Type} [Fintype n]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ρ : FramedGaloisRep K U n)
  (hne : flatReductionIdeal U v ρ ≠ ⊤) (p : ℕ)

/-- Nonnilpotence in the flat quotient is exactly exclusion of every power from its ideal. -/
theorem flatClosed_p_nonnilpotent_iff :
    ¬ IsNilpotent (p : flatClosedObject U v ρ hne) ↔
      ∀ m : ℕ, (p : U) ^ m ∉ flatReductionIdeal U v ρ := by
  change (¬ ∃ m : ℕ, (p : U ⧸ flatReductionIdeal U v ρ) ^ m = 0) ↔ _
  simp only [not_exists]
  apply forall_congr'
  intro m
  have he : (p : U ⧸ flatReductionIdeal U v ρ) ^ m =
      Ideal.Quotient.mk (flatReductionIdeal U v ρ) ((p : U) ^ m) := by
    simp only [map_pow, map_natCast]
  rw [he, Ideal.Quotient.eq_zero_iff_mem]

/-- An algebraic characteristic-zero specialization necessarily avoids all powers of p. -/
theorem flatClosed_powers_avoid_of_charZero {A : Type*} [CommRing A] [CharZero A]
    (f : flatClosedObject U v ρ hne →+* A) (hp : p ≠ 0) :
    ∀ m : ℕ, (p : U) ^ m ∉ flatReductionIdeal U v ρ := by
  apply (flatClosed_p_nonnilpotent_iff U v ρ hne p).mp
  rintro ⟨m, hm⟩
  have hz := congrArg f hm
  have hn : p ^ m ≠ 0 := pow_ne_zero m hp
  have hcast : ((p ^ m : ℕ) : A) ≠ 0 := Nat.cast_ne_zero.mpr hn
  apply hcast
  simpa only [map_pow, map_natCast, map_zero, Nat.cast_pow] using hz

omit [IsLocalRing O] [Finite (IsLocalRing.ResidueField O)] [Fintype n] in
/-- A vanishing power in the coefficient base already obstructs nonvanishing.
In particular a characteristic-p base cannot yield characteristic-zero solutions. -/
theorem flatReductionIdeal_contains_power_of_base [Finite n] (m : ℕ) (hm : (p : O) ^ m = 0) :
    (p : U) ^ m ∈ flatReductionIdeal U v ρ := by
  have hz := congrArg (algebraMap O U) hm
  have he : (p : U) ^ m = 0 := by
    simpa only [map_pow, map_natCast, map_zero] using hz
  rw [he]
  exact Ideal.zero_mem _

/-- Avoiding every power produces a prime of this quotient avoiding p.
Closedness, coefficient finiteness and an arithmetic nonvanishing proof are separate gates. -/
theorem flatClosed_exists_prime_avoiding_p
    (hpow : ∀ m : ℕ, (p : U) ^ m ∉ flatReductionIdeal U v ρ) :
    ∃ P : Ideal (flatClosedObject U v ρ hne), P.IsPrime ∧ (p : flatClosedObject U v ρ hne) ∉ P :=
  GaloisRepresentation.IsHardlyRamified.exists_prime_avoiding_p _ p
    ((flatClosed_p_nonnilpotent_iff U v ρ hne p).mpr hpow)

end Deformation

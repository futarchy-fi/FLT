/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.WittCoefficientFaithfulness
public import FLT.Deformations.FlatQuotientNonvanishing
public import Mathlib.Topology.Algebra.Module.Compact

/-!
# The characteristic-zero gate over the constructed Witt base

Powers avoiding the finite-flat ideal are equivalent to characteristic zero
of the entire effective quotient and to a continuous proartinian specialization
in characteristic zero. Under a separate Noetherian hypothesis, a continuous
domain specialization can also be constructed. Arithmetic nonvanishing and
finite-dimensional p-adic coefficient fields are not proved here.
-/

@[expose] public noncomputable section
open CategoryTheory NumberField
open scoped Deformation.WittCoefficients
namespace Deformation
open ProartinianCat
variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [Finite k]
  (U : ProartinianCat (WittVector p k))
  {K : Type} [Field K] [NumberField K] {n : Type} [Fintype n]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ρ : FramedGaloisRep K U n)
  (hne : flatReductionIdeal U v ρ ≠ ⊤)
local notation "Q" => flatClosedObject U v ρ hne

/-- Over W(k), the exact ideal avoidance condition gives characteristic zero on the quotient. -/
theorem wittFlat_charZero_iff :
    CharZero Q ↔ ∀ m : ℕ, (p : U) ^ m ∉ flatReductionIdeal U v ρ :=
  (WittCoefficients.charZero_iff p k Q).trans
    (flatClosed_p_nonnilpotent_iff U v ρ hne p)

/-- Existence in the proartinian category is precisely the same nonvanishing gate. -/
theorem wittFlat_exists_charZero_iff :
    (∃ A : ProartinianCat (WittVector p k), CharZero A ∧ Nonempty (Q ⟶ A)) ↔
      ∀ m : ℕ, (p : U) ^ m ∉ flatReductionIdeal U v ρ := by
  constructor
  · rintro ⟨A, hA, ⟨f⟩⟩
    let := hA
    exact flatClosed_powers_avoid_of_charZero U v ρ hne p f.hom.toRingHom
      (Fact.out : p.Prime).ne_zero
  · intro h
    exact ⟨Q, (wittFlat_charZero_iff p k U v ρ hne).mpr h, ⟨𝟙 Q⟩⟩

/-- If the effective quotient is Noetherian, a prime avoiding p is automatically closed. -/
theorem wittFlat_exists_closed_prime [IsNoetherianRing Q]
    (hpow : ∀ m : ℕ, (p : U) ^ m ∉ flatReductionIdeal U v ρ) :
    ∃ P : Ideal Q, P.IsPrime ∧ IsClosed (P : Set Q) ∧ (p : Q) ∉ P := by
  obtain ⟨P, hP, hp⟩ := flatClosed_exists_prime_avoiding_p U v ρ hne p hpow
  exact ⟨P, hP, IsNoetherianRing.isClosed_ideal P, hp⟩

/-- A closed prime produces an actual continuous characteristic-zero domain specialization. -/
theorem wittFlat_exists_domain [IsNoetherianRing Q]
    (hpow : ∀ m : ℕ, (p : U) ^ m ∉ flatReductionIdeal U v ρ) :
    ∃ A : ProartinianCat (WittVector p k), IsDomain A ∧ CharZero A ∧
      ∃ f : Q ⟶ A, Function.Surjective f.hom := by
  obtain ⟨P, hP, hc, hp⟩ := wittFlat_exists_closed_prime p k U v ρ hne hpow
  let := hP
  let A := closedIdealQuotient Q P hc hP.ne_top
  refine ⟨A, ?_, ?_, closedIdealQuotientHom Q P hc hP.ne_top,
    Ideal.Quotient.mk_surjective⟩
  · exact inferInstanceAs (IsDomain (Q ⧸ P))
  · exact WittCoefficients.primeQuotient_charZero p k Q P hp

end Deformation

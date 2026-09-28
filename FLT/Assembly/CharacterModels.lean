/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Assembly.CharacterConjugation
public import FLT.Assembly.CharacterModelPurity
public import FLT.GaloisRepresentation.HardlyRamified.CharacterSeparation
public import FLT.GaloisRepresentation.HardlyRamified.IntegralCharacters

/-!
# Integral character purity from sorted models at every level

The models carry the actual quotient character action. Scalar complex
conjugation makes each sorted model pure, and separation in ideal-power
quotients identifies the original integral character.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

local notation "Γ" => Field.absoluteGaloisGroup ℚ

/-- Sorted integral models at every coefficient level force an integral character
 to be trivial or cyclotomic. -/
theorem character_eq_one_or_cyclotomic_of_sorted_models
    {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[3] O]
    (I : Ideal O) [IsHausdorff I O] (hthree : (3 : O) ∈ I) (ψ : Γ →* Oˣ)
    (hmodels : ∀ n : ℕ,
      ∃ (H : FiniteFlatObject ZInvTwo) (_ : Module ℤ_[3] H.points)
        (_ : SortedFiniteFlatExtension H) (e : H.points ≃ₗ[ℤ_[3]] (O ⧸ I ^ n)),
        ∀ (σ : Γ) (x : H.points),
          e (σ • x) = Ideal.Quotient.mk (I ^ n) (ψ σ : O) * e x) :
    ψ = 1 ∨ ψ = threeAdicCyclotomic := by
  apply character_eq_one_or_of_each_power_quotient I ψ threeAdicCyclotomic
  intro n
  obtain ⟨H, instModule, S, e, he⟩ := hmodels n
  have hcast : (3 : O ⧸ I ^ n) ^ n = 0 := by
    simpa only [map_pow, map_ofNat] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hthree n))
  have hkill (x : H.points) : (3 ^ n) • x = 0 := by
    apply e.injective
    rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul (O ⧸ I ^ n),
      Nat.cast_pow, Nat.cast_ofNat, hcast, zero_smul]
  have hconj : (∀ x : H.points, rationalComplexConjugation • x = x) ∨
      (∀ x : H.points, rationalComplexConjugation • x = -x) := by
    rcases character_conjugation_of_domain ψ with h | h
    · left
      intro x
      apply e.injective
      rw [he, h, map_one, one_mul]
    · right
      intro x
      apply e.injective
      rw [he, h, map_neg, map_one, neg_one_mul, map_neg]
  rcases S.pure_of_scalar_conjugation n hkill hconj with hpure | hpure
  · left
    intro σ
    obtain ⟨x, hx⟩ := e.surjective 1
    have hh : e (σ • x) = e x := congrArg e (by simpa using hpure σ x)
    rwa [he, hx, mul_one] at hh
  · right
    intro σ
    obtain ⟨x, hx⟩ := e.surjective 1
    have hh := congrArg e (hpure σ x)
    rw [he, e.map_smul, hx, mul_one, Algebra.smul_def, mul_one] at hh
    change Ideal.Quotient.mk (I ^ n) (ψ σ : O) =
      algebraMap O (O ⧸ I ^ n)
        (algebraMap ℤ_[3] O
          (cyclotomicCharacter (AlgebraicClosure ℚ) 3 σ.toRingEquiv).val)
    rw [← IsScalarTower.algebraMap_apply ℤ_[3] O (O ⧸ I ^ n)]
    exact hh

end ThreeAdicPlan

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.RootCharacterExponent
public import FLT.AbsoluteGaloisGroup.NiveauTwoInertiaGenerator
public import FLT.GaloisRepresentation.SerreWeight.NiveauTwoDigits

/-!
# Normalizing niveau-two characters on actual inertia

Extract the two digits from a character of the constructed degree p²−1
root quotient. If it is not Frobenius-fixed, one of the two conjugates is
`theta^(a*(p+1)+b)` with `a < p-1` and `1 ≤ b < p`. The power p+1 is the
actual cyclotomic character. This does not prove that every irreducible
residual representation has this inertia type.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.SerreWeight

/-- A character on a cyclic group of niveau-two order has normalized conjugate digits. -/
theorem cyclic_character_niveauTwo_normalization
    {G C : Type*} [Group G] [CommGroup C] [Finite C] [IsCyclic C]
    {p : ℕ} (hp : 1 < p) (hcard : Nat.card C = p * p - 1)
    (θ χ : G →* C) (hθ : Function.Surjective θ) (hker : θ.ker ≤ χ.ker)
    (hne : χ ^ p ≠ χ) :
    ∃ a b : ℕ, a < p - 1 ∧ 1 ≤ b ∧ b < p ∧
      (χ = θ ^ (a * (p + 1) + b) ∨ χ ^ p = θ ^ (a * (p + 1) + b)) := by
  let := Fintype.ofFinite C
  obtain ⟨e, ⟨he, hχ⟩, _⟩ := existsUnique_cyclic_character_exponent θ χ hθ hker
  have he' : e < p * p - 1 := by rwa [hcard] at he
  have hnf : (p * e) % (p * p - 1) ≠ e := by
    intro hf
    apply hne
    ext g
    change χ g ^ p = χ g
    rw [hχ, ← pow_mul, Nat.mul_comm e p]
    calc
      θ g ^ (p * e) = θ g ^ ((p * e) % (p * p - 1)) := by
        simpa only [← hcard, Nat.card_eq_fintype_card] using
          (pow_mod_card (θ g) (p * e)).symm
      _ = θ g ^ e := congrArg (θ g ^ ·) hf
  obtain ⟨a, b, ha, hb, hb', h⟩ := exists_normalized_niveauTwo_digits hp he' hnf
  refine ⟨a, b, ha, hb, hb', ?_⟩
  rcases h with h | h
  · left
    ext g
    exact (hχ g).trans (congrArg (θ g ^ ·) h)
  · right
    ext g
    change χ g ^ p = θ g ^ (a * (p + 1) + b)
    rw [hχ, ← pow_mul, Nat.mul_comm e p, ← h]
    simpa only [← hcard, Nat.card_eq_fintype_card] using (pow_mod_card (θ g) (p * e)).symm

end GaloisRepresentation.SerreWeight

namespace LocalRoot
open IsLocalRing GaloisRepresentation.SerreWeight
variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "Ω" => AlgebraicClosure Kv
local notation "k" => ResidueField (IntegralClosure O Ω)
attribute [local instance] rationalResidue_charP

/-- Actual inertia characters factoring through the root quotient admit the normalized pair. -/
theorem niveauTwo_rootCharacter_normalization {π : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hn : 0 < p * p - 1)
    (hα : α ^ (p * p - 1) = algebraMap Kv Ω π.1)
    (χ : localInertiaGroup v →* rootsOfUnity (p * p - 1) k)
    (hker : (rootCharacterToRoots v hn hπ hα).ker ≤ χ.ker) (hne : χ ^ p ≠ χ) :
    ∃ a b : ℕ, a < p - 1 ∧ 1 ≤ b ∧ b < p ∧
      (χ = (rootCharacterToRoots v hn hπ hα) ^ (a * (p + 1) + b) ∨
        χ ^ p = (rootCharacterToRoots v hn hπ hα) ^ (a * (p + 1) + b)) := by
  have hp := (Fact.out : p.Prime).one_lt
  let : NeZero (p * p - 1) := ⟨hn.ne'⟩
  let : NeZero ((p * p - 1 : ℕ) : k) := ⟨by
    rw [Nat.cast_sub (by nlinarith : 1 ≤ p * p), Nat.cast_mul, Nat.cast_one,
      CharP.cast_eq_zero k p, zero_mul, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero⟩
  let : IsAlgClosed k := residue_isAlgClosed v
  exact cyclic_character_niveauTwo_normalization hp
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity k (p * p - 1)) (rootCharacterToRoots v hn hπ hα) χ
    (rootCharacterToRoots_surjective v hn hπ hα) hker hne

/-- The determinant-twist factor in the normalized expression is actual cyclotomic. -/
theorem niveauTwo_normalized_power {π : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hn : 0 < p * p - 1)
    (hα : α ^ (p * p - 1) = algebraMap Kv Ω π.1)
    (a b : ℕ) (σ : localInertiaGroup v) :
    ((rootCharacterToRoots v hn hπ hα σ : rootsOfUnity (p * p - 1) k) : kˣ) ^
        (a * (p + 1) + b) = residueCyclotomic p σ ^ a *
          ((rootCharacterToRoots v hn hπ hα σ : rootsOfUnity (p * p - 1) k) : kˣ) ^ b := by
  change character v hn _ hα σ ^ (a * (p + 1) + b) = _
  rw [pow_add, Nat.mul_comm a, pow_mul,
    character_two_norm_eq_residueCyclotomic p hπ hn hα σ]
  rfl

end LocalRoot

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.RootCharacterCyclotomicNorm
public import FLT.AbsoluteGaloisGroup.RootCharacterGenerator
public import FLT.Deformations.RepresentationTheory.TameSpectrumDigits

/-!
# A niveau-two generator with its actual cyclotomic norm

Select the original inertia element using the degree p²−1 root character.
The cyclotomic generator and ratio orders follow for that same element.
-/

@[expose] public noncomputable section
namespace LocalRoot
open IsLocalRing

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "Ω" => AlgebraicClosure Kv
local notation "k" => ResidueField (IntegralClosure O Ω)
attribute [local instance] rationalResidue_charP

/-- The geometric-residue embedding preserves the order of actual cyclotomic values. -/
theorem residueCyclotomic_order (σ : localInertiaGroup v) :
    orderOf (residueCyclotomic p σ) = orderOf (modCyclotomic p σ.1) :=
  orderOf_injective _ (Units.map_injective (ZMod.castHom (dvd_refl p) k).injective) _

/-- Choose a full niveau-two generator, then derive the cyclotomic and ratio orders. -/
theorem exists_niveauTwo_inertia_generator {π : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hn : 0 < p * p - 1)
    (hα : α ^ (p * p - 1) = algebraMap Kv Ω π.1) :
    ∃ σ : localInertiaGroup v,
      let z := character v hn
        (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
          hπ (Subtype.ext h)) hα σ
      orderOf z = p * p - 1 ∧
      z ^ (p + 1) = residueCyclotomic p σ ∧
      orderOf (modCyclotomic p σ.1) = p - 1 ∧
      orderOf (z / z ^ p) = p + 1 := by
  have hp := (Fact.out : p.Prime).one_lt
  have hnk : ((p * p - 1 : ℕ) : k) ≠ 0 := by
    rw [Nat.cast_sub (by nlinarith : 1 ≤ p * p), Nat.cast_mul, Nat.cast_one,
      CharP.cast_eq_zero k p, zero_mul, zero_sub]
    exact neg_ne_zero.mpr one_ne_zero
  obtain ⟨σ, hσ⟩ := exists_rootCharacter_generator v hn hnk hπ hα
  have hc := character_two_norm_eq_residueCyclotomic p hπ hn hα σ
  refine ⟨σ, hσ, hc, ?_, Representation.niveau_two_ratio_order hp hσ⟩
  rw [← residueCyclotomic_order p σ, ← hc]
  exact Representation.niveau_two_norm_order hp hσ

/-- A full root and a compatible inertia generator exist for every uniformizer. -/
theorem exists_niveauTwo_root_and_generator {π : O}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ (α : Ω) (hn : 0 < p * p - 1)
      (hα : α ^ (p * p - 1) = algebraMap Kv Ω π.1) (σ : localInertiaGroup v),
      orderOf (character v hn
        (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
          hπ (Subtype.ext h)) hα σ) = p * p - 1 ∧
      orderOf (modCyclotomic p σ.1) = p - 1 := by
  have hp := (Fact.out : p.Prime).one_lt
  have hn : 0 < p * p - 1 := Nat.sub_pos_of_lt (by nlinarith)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap Kv Ω π.1) hn
  obtain ⟨σ, hs, _, hc, _⟩ := exists_niveauTwo_inertia_generator p hπ hn hα
  exact ⟨α, hn, hα, σ, hs, hc⟩

end LocalRoot

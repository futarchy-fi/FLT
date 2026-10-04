/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.NiveauTwoInertiaCharacter
public import FLT.AbsoluteGaloisGroup.NiveauTwoCharacterNormalization
public import FLT.AbsoluteGaloisGroup.RootCharacterKernel

/-!
# Normalized niveau-two characters extracted from an inertia representation

For a continuous simple rank-two prime-field inertia action, construct the
actual eigencharacter, prove root-kernel containment, and normalize one of
its two Frobenius orientations. Neither the character, kernel containment,
nor non-Frobenius-fixedness is supplied as an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LocalRoot
open IsLocalRing Polynomial

variable (p : ℕ) [Fact p.Prime]
local notation "v" => LocalCyclotomic.rationalPlace p
local notation "Kv" => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "O" => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "Ω" => AlgebraicClosure Kv
local notation "k" => ResidueField (IntegralClosure O Ω)
attribute [local instance] rationalResidue_charP

variable {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  (ρ : Representation (ZMod p) (localInertiaGroup (LocalCyclotomic.rationalPlace p)) V)
  [ρ.IsIrreducible]
  [TopologicalSpace (Module.End (ZMod p) V)ˣ]
  [DiscreteTopology (Module.End (ZMod p) V)ˣ]

set_option maxHeartbeats 800000 in
-- Rational-completion and absolute-residue instances need extra elaboration time.
/-- Extract and normalize a genuine niveau-two inertia character, proving the kernel gate. -/
theorem exists_normalized_niveauTwo_inertia_character
    (hρ : Continuous ρ.toHomUnits) (hV : Module.finrank (ZMod p) V = 2)
    {π : O} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hn : 0 < p * p - 1)
    (hα : α ^ (p * p - 1) = algebraMap Kv Ω π.1) :
    ∃ (χ : localInertiaGroup v →* rootsOfUnity (p * p - 1) k) (a b : ℕ),
      χ.ker = ρ.toHomUnits.ker ∧
      (rootCharacterToRoots v hn hπ hα).ker ≤ ρ.toHomUnits.ker ∧
      χ ^ p ≠ χ ∧ a < p - 1 ∧ 1 ≤ b ∧ b < p ∧
      (χ = (rootCharacterToRoots v hn hπ hα) ^ (a * (p + 1) + b) ∨
        χ ^ p = (rootCharacterToRoots v hn hπ hα) ^ (a * (p + 1) + b)) ∧
      ∀ g, (ρ g).charpoly.map (ZMod.castHom (dvd_refl p) k) =
        (X - C ((χ g : kˣ) : k)) * (X - C (((χ g : kˣ) : k) ^ p)) := by
  let : CharP (ResidueField O) p := charP_of_injective_ringHom
    (LocalCyclotomic.residueEquiv p).symm.toRingHom.injective p
  have hex := LocalRamification.exists_niveauTwo_inertia_character (K := ℚ) v p ρ hρ hV
  obtain ⟨χ, hk, ho, hne, hc⟩ := hex
  have hp := (Fact.out : p.Prime)
  have hpn : p.Coprime (p * p - 1) := by
    have hpp : 1 ≤ p * p := by nlinarith [hp.two_le]
    exact ((Nat.coprime_self_sub_right hpp).mpr (Nat.coprime_one_right (p * p))).of_dvd_left
      (dvd_mul_right p p)
  have hker := rootCharacter_ker_le_of_isOpen v hp hn hpn hπ hα χ ho
  obtain ⟨a, b, ha, hb, hb', he⟩ := niveauTwo_rootCharacter_normalization p hπ hn hα χ hker hne
  exact ⟨χ, a, b, hk, hker.trans hk.le, hne, ha, hb, hb', he, hc⟩

end LocalRoot

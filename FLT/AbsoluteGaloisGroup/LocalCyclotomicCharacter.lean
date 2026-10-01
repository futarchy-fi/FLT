/-
Copyright (c) 2026 Kelvin Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kelvin Santos
-/
module

public import FLT.AbsoluteGaloisGroup.LocalCyclotomicRamification
public import FLT.AbsoluteGaloisGroup.TameCharacter
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclotomic characters on finite local extensions

The actual modular cyclotomic character on the finite cyclotomic Galois group
is surjective, and a Galois element with generating value is constructed.
Naturality under field embeddings and the reduction of the cyclotomic
uniformizer ratio are recorded separately. These results do not yet lift the
finite Galois element to local absolute inertia or identify the tame character.
-/

@[expose] public noncomputable section

namespace LocalCyclotomic

variable (p : ℕ) [Fact p.Prime] (E : Type*) [Field E] [Algebra ℚ_[p] E]
  [IsCyclotomicExtension {p} ℚ_[p] E]

/-- The mod-p cyclotomic character on the finite local cyclotomic extension. -/
def character : Gal(E/ℚ_[p]) →* (ZMod p)ˣ :=
  (modularCyclotomicCharacter E
    (IsCyclotomicExtension.zeta_spec p ℚ_[p] E).card_rootsOfUnity).comp
      { toFun := fun σ ↦ σ.toRingEquiv
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl }

/-- This is the standard cyclotomic Galois equivalence, with no change of character. -/
theorem character_eq_autEquivPow :
    character p E = (IsCyclotomicExtension.autEquivPow E
      (cyclotomic_irreducible p)).toMonoidHom := by
  ext σ
  exact congrArg Units.val
    ((IsCyclotomicExtension.zeta_spec p ℚ_[p] E).autToPow_eq_modularCyclotomicCharacter
      p ℚ_[p] σ).symm

/-- The finite local cyclotomic character attains every residue-field unit. -/
theorem character_surjective : Function.Surjective (character p E) := by
  rw [character_eq_autEquivPow]
  exact (IsCyclotomicExtension.autEquivPow E (cyclotomic_irreducible p)).surjective

/-- A finite local Galois element with generating cyclotomic value. -/
theorem exists_character_generator :
    ∃ σ : Gal(E/ℚ_[p]), ∀ a : (ZMod p)ˣ, a ∈ Subgroup.zpowers (character p E σ) := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  obtain ⟨σ, hσ⟩ := character_surjective p E a
  exact ⟨σ, hσ ▸ ha⟩

/-- The rational place corresponding to p, in the p-adic comparison API. -/
def rationalPlace : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm
    ⟨p, Fact.out⟩

/-- The residue field at the rational p-adic place identified with `ZMod p`. -/
def residueEquiv :
    IsLocalRing.ResidueField ((rationalPlace p).adicCompletionIntegers ℚ) ≃+* ZMod p :=
  (IsLocalRing.ResidueField.mapEquiv
    (PadicInt.adicCompletionIntegersEquiv (NumberField.RingOfIntegers ℚ)
      ⟨p, Fact.out⟩).symm.toAlgEquiv.toRingEquiv).trans PadicInt.residueField

/-- The residue cardinality used in the tame character is exactly p. -/
theorem residue_natCard :
    Nat.card (IsLocalRing.ResidueField ((rationalPlace p).adicCompletionIntegers ℚ)) = p := by
  rw [Nat.card_congr (residueEquiv p).toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-- The mod-p cyclotomic character restricted to local absolute inertia. -/
def inertiaCharacter : localInertiaGroup (rationalPlace p) →* (ZMod p)ˣ :=
  (modularCyclotomicCharacter (AlgebraicClosure ((rationalPlace p).adicCompletion ℚ))
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ p)).comp
      { toFun := fun σ ↦ σ.1.toRingEquiv
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl }

end LocalCyclotomic

namespace modularCyclotomicCharacter

variable {L M : Type*} [Field L] [Field M] {n : ℕ} [NeZero n]

/-- The modular cyclotomic character is compatible with an equivariant field embedding. -/
theorem naturality (f : L →+* M) (σ : L ≃+* L) (τ : M ≃+* M)
    (hcomm : ∀ x, f (σ x) = τ (f x))
    (hL : Nat.card (rootsOfUnity n L) = n) (hM : Nat.card (rootsOfUnity n M) = n) :
    modularCyclotomicCharacter L hL σ = modularCyclotomicCharacter M hM τ := by
  apply Units.ext
  symm
  apply unique L hL σ
  intro t ht
  apply f.injective
  rw [map_pow, hcomm]
  have htM : Units.map f.toMonoidHom t ∈ rootsOfUnity n M := by
    rw [mem_rootsOfUnity] at ht ⊢
    simp only [← map_pow, ht, map_one]
  exact spec M hM τ htM

end modularCyclotomicCharacter

namespace LocalCyclotomic

/-- Reduction of the geometric-sum expression for `(ζ^a - 1)/(ζ - 1)`.
This formula uses only that the reduction of ζ is one. -/
theorem map_cyclotomic_ratio {S k L : Type*} [CommRing S] [Field k] [Field L]
    (r : S →+* k) (i : S →+* L) {ζ : S} (hζ : i ζ ≠ 1) (hr : r ζ = 1)
    (a : ℕ) :
    i (∑ j ∈ Finset.range a, ζ ^ j) = ((i ζ) ^ a - 1) / (i ζ - 1) ∧
      r (∑ j ∈ Finset.range a, ζ ^ j) = (a : k) := by
  constructor
  · apply (eq_div_iff (sub_ne_zero.mpr hζ)).mpr
    simpa only [map_sum, map_pow] using geom_sum_mul (i ζ) a
  · simp [hr]

end LocalCyclotomic

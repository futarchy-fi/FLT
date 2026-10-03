/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FrobeniusPowers

/-!
# Frobenius comparison across integral base change

A commuting integral embedding compares the two residue power rules.
The cardinality formula for finite residue fields supplies the residue-degree
exponent, without any unramifiedness assumption on the base extension.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S A B K L E F : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Field K] [Field L] [Field E] [Field F]
  [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
  [Algebra A E] [IsFractionRing A E] [Algebra B F] [IsFractionRing B F]
  [Algebra R A] [Algebra K E] [Algebra R E]
  [IsScalarTower R K E] [IsScalarTower R A E] [IsIntegralClosure A R E]
  [Algebra S B] [Algebra L F] [Algebra S F]
  [IsScalarTower S L F] [IsScalarTower S B F] [IsIntegralClosure B S F]
  [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional L F] [IsGalois L F]
  [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap S B)]
  [Algebra.FormallyUnramified R A] [Algebra.FormallyUnramified S B]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Finite (ResidueField R)] [Finite (ResidueField S)]

/-- An integral embedding commuting with Frobenius forces the residue-degree power
on the original unramified extension. -/
theorem integralFrobenius_baseChange (i : A →+* B) [IsLocalHom i] (σ : Gal(E/K))
    (hi : ∀ x : A, i (galRestrict R K E A σ x) =
      galRestrict S L F B (arithmeticFrobenius S B L F) (i x)) :
    σ = arithmeticFrobenius R A K E ^
      Module.finrank (ResidueField R) (ResidueField S) := by
  apply arithmeticFrobenius_pow_unique R A K E
  intro x
  apply (ResidueField.map i).injective
  rw [ResidueField.map_residue, map_pow, ResidueField.map_residue, hi,
    arithmeticFrobenius_residue_integral]
  rw [Module.natCard_eq_pow_finrank (K := ResidueField R) (V := ResidueField S)]

end LocalClassFieldTheory

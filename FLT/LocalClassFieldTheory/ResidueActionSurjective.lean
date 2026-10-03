/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ResidueAction
public import Mathlib.RingTheory.Invariant.Basic

/-!
# Surjectivity of reduction for finite invariant local algebras

The existing ideal-stabilizer theorem supplies every residue automorphism.
Its preimage is an automorphism of the original local algebra.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)]
  [Finite (S ≃ₐ[R] S)] [Algebra.IsInvariant R S (S ≃ₐ[R] S)]

/-- Every automorphism of the residue extension lifts for a finite invariant
local algebra. In a Galois integral closure, invariance is a theorem. -/
theorem residueAction_surjective : Function.Surjective (residueAction R S) := by
  intro σ
  obtain ⟨τ, hτ⟩ := Ideal.Quotient.stabilizerHom_surjective
    (S ≃ₐ[R] S) (maximalIdeal R) (maximalIdeal S) σ
  refine ⟨τ.1, ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := residue_surjective x
  exact congrArg (fun e => e (residue S x)) hτ

end LocalClassFieldTheory

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.LocalCyclotomicCharacter
public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Naturality of the p-adic cyclotomic character -/

@[expose] public noncomputable section
namespace cyclotomicCharacter
variable {L M : Type*} [Field L] [Field M] (p : ℕ) [Fact p.Prime]
  [∀ i, HasEnoughRootsOfUnity L (p ^ i)] [∀ i, HasEnoughRootsOfUnity M (p ^ i)]

/-- An equivariant field embedding preserves the full p-adic cyclotomic character. -/
theorem naturality (f : L →+* M) (σ : L ≃+* L) (τ : M ≃+* M)
    (hcomm : ∀ x, f (σ x) = τ (f x)) :
    cyclotomicCharacter L p σ = cyclotomicCharacter M p τ := by
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  rw [cyclotomicCharacter.toZModPow, cyclotomicCharacter.toZModPow]
  exact congrArg Units.val (modularCyclotomicCharacter.naturality f σ τ hcomm _ _)

/-- The actual absolute-Galois restriction map preserves cyclotomic characters. -/
theorem absoluteGalois_map {K E : Type*} [Field K] [Field E] [CharZero K] [CharZero E]
    (f : K →+* E) (g : Field.absoluteGaloisGroup E) :
    cyclotomicCharacter (AlgebraicClosure K) p (Field.absoluteGaloisGroup.map f g).toRingEquiv =
      cyclotomicCharacter (AlgebraicClosure E) p g.toRingEquiv := by
  apply naturality p (AlgebraicClosure.map f)
  exact Field.absoluteGaloisGroup.lift_map f g

end cyclotomicCharacter

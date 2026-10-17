/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionFlatDescent
public import FLT.Mazur.AdicCompletionPositiveEquiv

/-!
# Original algebra flatness from all finite inverses and the generic map

Equivalences of the positive adic quotients over the original source algebra
automatically retain every transition. Their limit supplies completed flatness,
and completion together with parameter inversion descends it to the algebra.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AdicQuotientFlatCriterion
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (I : Ideal A) (J : Ideal B)
  (e : ∀ m : ℕ, (A ⧸ I ^ (m + 1)) ≃ₐ[A] (B ⧸ J ^ (m + 1)))

/-- Source-algebra linearity forces compatibility of the actual positive quotient inverses. -/
theorem compatible (m : ℕ) (x : A ⧸ I ^ (m + 2)) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))) (e (m + 1) x) =
      e m (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))) x) := by
  induction x using Quotient.inductionOn' with
  | _ a =>
    change Ideal.Quotient.factor _ (e (m + 1) (algebraMap A _ a)) =
      e m (algebraMap A _ a)
    rw [AlgEquiv.commutes, AlgEquiv.commutes]
    rfl

/-- The compatible finite inverses identify the completions over the unchanged source algebra. -/
def equivalence : AdicCompletion I A ≃ₐ[A] AdicCompletion J B :=
  AdicCompletionPositiveEquiv.equivalence I J e (compatible I J e)

variable [IsNoetherianRing A]

include I e in
/-- The target completion is flat over the original source, not only its coefficient ring. -/
theorem completion_flat : Module.Flat A (AdicCompletion J B) :=
  Module.Flat.of_linearEquiv (equivalence I J e).symm.toLinearEquiv

variable [IsNoetherianRing B]

/-- Finite original inverses and generic flatness imply flatness before completion. -/
theorem flat_of_quotient_equivalences (t : B)
    (e : ∀ m : ℕ, (A ⧸ I ^ (m + 1)) ≃ₐ[A]
      (B ⧸ Ideal.span {t} ^ (m + 1)))
    (hg : ((algebraMap B (Localization.Away t)).comp (algebraMap A B)).Flat) :
    Module.Flat A B := by
  apply RingHom.flat_algebraMap_iff.mp
  apply AdicCompletionFlatDescent.flat_of_completion_and_away (algebraMap A B) t
  · rw [← IsScalarTower.algebraMap_eq A B (AdicCompletion (Ideal.span {t}) B)]
    exact RingHom.flat_algebraMap_iff.mpr (completion_flat I (Ideal.span {t}) e)
  · exact hg

end FLT.Mazur.AdicQuotientFlatCriterion

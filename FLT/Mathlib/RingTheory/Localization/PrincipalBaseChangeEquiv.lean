/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Localization.BaseChange

/-! # Principal localization of a specified base-change comparison -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace IsLocalization.Away

variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra S B]

/-- Localize an algebra base-change equivalence at a specified element and its image. -/
def baseChangeEquiv (e : (S ⊗[R] A) ≃ₐ[S] B) (a : A) (b : B)
    (h : e (1 ⊗ₜ[R] a) = b) :
    (S ⊗[R] Localization.Away a) ≃ₐ[S] Localization.Away b :=
  (tensorProductEquivTMulRight R S a (Localization.Away a)).trans
    (IsLocalization.algEquivOfAlgEquiv
      (M := Submonoid.powers ((1 : S) ⊗ₜ[R] a)) (T := Submonoid.powers b)
      (Localization.Away ((1 : S) ⊗ₜ[R] a)) (Localization.Away b) e
      (by rw [Submonoid.map_powers, h]))

/-- The localized comparison retains the original algebra representatives. -/
@[simp] theorem baseChangeEquiv_tmul (e : (S ⊗[R] A) ≃ₐ[S] B) (a : A) (b : B)
    (h : e (1 ⊗ₜ[R] a) = b) (s : S) (x : A) :
    baseChangeEquiv e a b h (s ⊗ₜ[R] algebraMap A (Localization.Away a) x) =
      algebraMap B (Localization.Away b) (e (s ⊗ₜ[R] x)) := by
  simp only [baseChangeEquiv, AlgEquiv.trans_apply, tensorProductEquivTMulRight_tmul,
    IsLocalization.algEquivOfAlgEquiv_eq]

end IsLocalization.Away

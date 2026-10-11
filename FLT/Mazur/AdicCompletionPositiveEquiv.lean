/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionQuotientEquiv

/-!
# Completion from adjacent compatible positive-power algebra equivalences

Adjacent compatibility supplies all transitions. The zeroth quotient is the
zero algebra and is reconstructed uniquely before forming the completion.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicCompletionPositiveEquiv

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] (I : Ideal A) (J : Ideal B)

/-- Both zeroth ideal-power quotients are the zero algebra. -/
def zeroEquiv : (A ⧸ I ^ 0) ≃ₐ[K] (B ⧸ J ^ 0) := by
  let _ : Subsingleton (A ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
  let _ : Subsingleton (B ⧸ J ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
  exact
    { toFun := fun _ ↦ 0
      invFun := fun _ ↦ 0
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _
      map_mul' := fun _ _ ↦ Subsingleton.elim _ _
      map_add' := fun _ _ ↦ Subsingleton.elim _ _
      commutes' := fun _ ↦ Subsingleton.elim _ _ }

variable (e : ∀ m : ℕ, (A ⧸ I ^ (m + 1)) ≃ₐ[K] (B ⧸ J ^ (m + 1)))
  (he : ∀ (m : ℕ) (a : A ⧸ I ^ (m + 2)),
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))) (e (m + 1) a) =
      e m (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))) a))

include he in
/-- Adjacent compatibility implies compatibility of every positive-power transition. -/
theorem compatible {m n : ℕ} (hmn : m ≤ n) (a : A ⧸ I ^ (n + 1)) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)) (e n a) =
      e m (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)) a) := by
  induction n, hmn using Nat.le_induction with
  | base => simp only [Ideal.Quotient.factor_eq, RingHom.id_apply]
  | succ n hmn ih =>
    have hj := Ideal.pow_le_pow_right (I := J) (Nat.add_le_add_right hmn 1)
    have hi := Ideal.pow_le_pow_right (I := I) (Nat.add_le_add_right hmn 1)
    rw [← Ideal.Quotient.factor_comp_apply
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) hj, he, ih,
      Ideal.Quotient.factor_comp_apply _ hi]

/-- Reconstruct the uniquely determined zeroth quotient alongside the positive quotients. -/
def atPower : ∀ r : ℕ, (A ⧸ I ^ r) ≃ₐ[K] (B ⧸ J ^ r)
  | 0 => zeroEquiv I J
  | m + 1 => e m

include he in
/-- The reconstructed quotient algebra equivalences retain every transition. -/
theorem atPower_compatible {m n : ℕ} (hmn : m ≤ n) (a : A ⧸ I ^ n) :
    Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hmn) (atPower I J e n a) =
      atPower I J e m (Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hmn) a) := by
  cases m with
  | zero =>
    let _ : Subsingleton (B ⧸ J ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact Subsingleton.elim _ _
  | succ m =>
    cases n with
    | zero => omega
    | succ n => exact compatible I J e he (Nat.le_of_succ_le_succ hmn) a

/-- The actual completions are isomorphic over the original scalar ring. -/
def equivalence : AdicCompletion I A ≃ₐ[K] AdicCompletion J B :=
  AdicCompletionQuotientEquiv.equivalence I J (atPower I J e)
    (atPower_compatible I J e he)

/-- The completion equivalence retains precisely the given positive-power comparisons. -/
@[simp] theorem eval_equivalence (m : ℕ) (a : AdicCompletion I A) :
    AdicCompletion.evalₐ J (m + 1) (equivalence I J e he a) =
      e m (AdicCompletion.evalₐ I (m + 1) a) :=
  AdicCompletionQuotientEquiv.eval_map I J (atPower I J e)
    (atPower_compatible I J e he) (m + 1) a

end FLT.Mazur.AdicCompletionPositiveEquiv

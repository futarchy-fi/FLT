/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionAlgEquiv
/-!
# Completion from compatible quotient isomorphisms

Compatible algebra isomorphisms at every ideal power induce an algebra
isomorphism of the completion rings; their inverses are automatically compatible.
-/

open AdicCompletion
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.AdicCompletionQuotientEquiv
variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
variable (I : Ideal A) (J : Ideal B)
  (e : ∀ n : ℕ, (A ⧸ I ^ n) ≃ₐ[K] (B ⧸ J ^ n))
  (he : ∀ {m n : ℕ} (hmn : m ≤ n) (x : A ⧸ I ^ n),
    Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hmn) (e n x) =
      e m (Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hmn) x))
include he in
theorem compatible {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hmn)).comp
      ((e n).toAlgHom.comp ((evalₐ I n).restrictScalars K)) =
    (e m).toAlgHom.comp ((evalₐ I m).restrictScalars K) := by
  ext x
  change Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hmn)
    (e n (evalₐ I n x)) = e m (evalₐ I m x)
  rw [he hmn, AdicCompletionAlgEquiv.eval_compatible I hmn]
/-- The map on completion rings obtained from the compatible quotient maps. -/
def map : AdicCompletion I A →ₐ[K] AdicCompletion J B :=
  liftAlgHom J (fun n ↦ (e n).toAlgHom.comp ((evalₐ I n).restrictScalars K))
    (compatible I J e he)
@[simp] theorem eval_map (n : ℕ) (x : AdicCompletion I A) :
    evalₐ J n (map I J e he x) = e n (evalₐ I n x) :=
  AdicCompletion.evalₐ_liftAlgHom J _ (compatible I J e he) n x
include he in
theorem inverse_compatible {m n : ℕ} (hmn : m ≤ n) (x : B ⧸ J ^ n) :
    Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hmn) ((e n).symm x) =
      (e m).symm (Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hmn) x) := by
  apply (e m).injective
  rw [← he hmn, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
/-- Compatible isomorphisms at every ideal power identify the completed algebras. -/
def equivalence : AdicCompletion I A ≃ₐ[K] AdicCompletion J B :=
  { map I J e he with
    invFun := map J I (fun n ↦ (e n).symm) (inverse_compatible I J e he)
    left_inv := fun x ↦ by
      apply ext_evalₐ
      intro n
      change evalₐ I n (map J I (fun n ↦ (e n).symm) (inverse_compatible I J e he)
        (map I J e he x)) = _
      rw [eval_map, eval_map, AlgEquiv.symm_apply_apply]
    right_inv := fun x ↦ by
      apply ext_evalₐ
      intro n
      change evalₐ J n (map I J e he
        (map J I (fun n ↦ (e n).symm) (inverse_compatible I J e he) x)) = _
      rw [eval_map, eval_map, AlgEquiv.apply_symm_apply] }
end FLT.Mazur.AdicCompletionQuotientEquiv

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
/-!
# Algebra isomorphisms on adic completions

An algebra isomorphism carrying one ideal to another induces compatible
isomorphisms on all power quotients, hence on the inverse-limit rings.
In particular, local algebra isomorphisms preserve completed local rings.
-/

open AdicCompletion
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.AdicCompletionAlgEquiv
variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
theorem eval_compatible (I : Ideal A) {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hmn) (evalₐ I n x) = evalₐ I m x := by
  simp only [evalₐ, AlgHom.coe_comp, Function.comp_apply,
    Ideal.quotientEquivAlgOfEq_coe_eq_factorₐ]
  change Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
    (Ideal.Quotient.factor (by simp) (eval I A n x)) =
    Ideal.Quotient.factor (by simp) (eval I A m x)
  have ht := congrArg (Ideal.Quotient.factor (show I ^ m • ⊤ ≤ I ^ m by simp))
    (transitionMap_comp_eval_apply I A hmn x)
  convert ht using 1
  · change Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
      (Ideal.Quotient.factor (by simp) (x.val n)) = _
    generalize x.val n = y
    induction y using Quotient.inductionOn
    rfl
  · rfl
variable (e : A ≃ₐ[K] B) (I : Ideal A) (J : Ideal B) (h : J = I.map (e : A →+* B))
/-- The algebra isomorphism on each quotient by an ideal power. -/
def quotient (n : ℕ) : (A ⧸ I ^ n) ≃ₐ[K] (B ⧸ J ^ n) :=
  Ideal.quotientEquivAlg _ _ e (by rw [h, Ideal.map_pow])
theorem quotient_compatible {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hmn)).comp
      ((quotient e I J h n).toAlgHom.comp ((evalₐ I n).restrictScalars K)) =
    (quotient e I J h m).toAlgHom.comp ((evalₐ I m).restrictScalars K) := by
  ext x
  change Ideal.Quotient.factorₐ K (Ideal.pow_le_pow_right hmn)
    (quotient e I J h n (evalₐ I n x)) = quotient e I J h m (evalₐ I m x)
  rw [← eval_compatible (K := K) I hmn x]
  generalize evalₐ I n x = y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl
/-- The map of completion rings induced by the compatible quotient isomorphisms. -/
def map : AdicCompletion I A →ₐ[K] AdicCompletion J B :=
  liftAlgHom J (fun n ↦ (quotient e I J h n).toAlgHom.comp ((evalₐ I n).restrictScalars K))
    (quotient_compatible e I J h)
@[simp] theorem eval_map (n : ℕ) (x : AdicCompletion I A) :
    evalₐ J n (map e I J h x) = quotient e I J h n (evalₐ I n x) :=
  AdicCompletion.evalₐ_liftAlgHom J _ (quotient_compatible e I J h) n x

end FLT.Mazur.AdicCompletionAlgEquiv
namespace FLT.Mazur.AdicCompletionAlgEquiv
variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]
variable (e : A ≃ₐ[K] B) (I : Ideal A) (J : Ideal B) (h : J = I.map (e : A →+* B))
include h in
theorem reverse_ideal : I = J.map (e.symm : B →+* A) := by
  rw [h, Ideal.map_map]
  have he : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A := by ext x; simp
  rw [he, Ideal.map_id]
/-- The algebra isomorphism of completions induced by an ideal-preserving isomorphism. -/
def equivalence : AdicCompletion I A ≃ₐ[K] AdicCompletion J B :=
  { map e I J h with
    invFun := map e.symm J I (reverse_ideal e I J h)
    left_inv := fun x ↦ by
      apply ext_evalₐ
      intro n
      change evalₐ I n (map e.symm J I (reverse_ideal e I J h) (map e I J h x)) = _
      rw [eval_map, eval_map]
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
      rw [← ha]
      simp [quotient, Ideal.quotientEquivAlg_mk]
    right_inv := fun x ↦ by
      apply ext_evalₐ
      intro n
      change evalₐ J n (map e I J h (map e.symm J I (reverse_ideal e I J h) x)) = _
      rw [eval_map, eval_map]
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ J n x)
      rw [← hb]
      simp [quotient, Ideal.quotientEquivAlg_mk] }
end FLT.Mazur.AdicCompletionAlgEquiv

namespace FLT.Mazur.AdicCompletionAlgEquiv
variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [IsLocalRing A] [IsLocalRing B]
/-- A local algebra isomorphism induces an isomorphism on maximal-ideal completions. -/
def localEquivalence (e : A ≃ₐ[K] B) :
    AdicCompletion (IsLocalRing.maximalIdeal A) A ≃ₐ[K]
      AdicCompletion (IsLocalRing.maximalIdeal B) B :=
  equivalence e _ _ (IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv).symm
end FLT.Mazur.AdicCompletionAlgEquiv

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafSupportPower

/-!
# Stabilization of full ideal powers with open closed support

On a Noetherian scheme an ideal whose closed support is also open has
stationary powers. The proof uses the complementary closed support and
uniform nilpotence of the product; it retains the full nilpotent structure.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
namespace FLT.Mazur.IdealSheafClopenStabilization
open Scheme.IdealSheafData

private theorem pow_succ_eq_of_complement {R : Type*} [CommRing R]
    (I J : Ideal R) (h : I ⊔ J = ⊤) (N : ℕ) (hz : (I * J) ^ N = ⊥) :
    I ^ (N + 1) = I ^ N := by
  calc
    I ^ (N + 1) = I ^ (N + 1) ⊔ (I * J) ^ N := by rw [hz, sup_bot_eq]
    _ = I ^ N * (I ⊔ J ^ N) := by rw [Ideal.mul_sup, mul_pow, pow_succ]
    _ = I ^ N := by rw [Ideal.sup_pow_eq_top h, Ideal.mul_top]

/-- Open closed support gives one equality between consecutive full ideal powers. -/
theorem exists_pow_succ_eq {X : Scheme.{0}} [IsNoetherian X]
    (I : X.IdealSheafData) (hopen : IsOpen (I.support : Set X)) :
    ∃ K : ℕ, I ^ (K + 1 + 1) = I ^ (K + 1) := by
  let Z : TopologicalSpace.Closeds X := ⟨(I.support : Set X)ᶜ, hopen.isClosed_compl⟩
  let J := vanishingIdeal Z
  have hJ : J.support = Z := rfl
  have hsup : I ⊔ J = ⊤ := by
    apply (support_eq_bot_iff (I ⊔ J)).mp
    rw [support_sup, hJ]
    ext x
    change (x ∈ I.support ∧ x ∉ I.support) ↔ False
    simp
  have hprod : (I * J).support = ⊤ := by
    rw [support_mul, hJ]
    ext x
    change (x ∈ I.support ∨ x ∉ I.support) ↔ True
    exact iff_true_intro (Classical.em _)
  obtain ⟨K, hK⟩ := IdealSheafSupportPower.exists_pow_le_of_support (I * J) ⊥
    (by rw [support_bot, hprod])
  have hz : (I * J) ^ (K + 1) = ⊥ := le_antisymm hK bot_le
  refine ⟨K, ?_⟩
  ext U : 2
  apply pow_succ_eq_of_complement (I.ideal U) (J.ideal U)
  · exact congrArg (fun L : X.IdealSheafData ↦ L.ideal U) hsup
  · exact congrArg (fun L : X.IdealSheafData ↦ L.ideal U) hz

/-- Consecutive equality stabilizes every later full power, with one common threshold. -/
theorem powers_stable_of_succ_eq {X : Scheme.{0}} (I : X.IdealSheafData) (K : ℕ)
    (hK : I ^ (K + 1 + 1) = I ^ (K + 1)) :
    ∀ l, K ≤ l → I ^ (l + 1) = I ^ (K + 1) := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base => rfl
  | succ l _ ih => rw [pow_succ, ih, ← pow_succ, hK]

/-- Geometric support, rather than a supplied formal stabilization witness, suffices. -/
theorem exists_stable {X : Scheme.{0}} [IsNoetherian X]
    (I : X.IdealSheafData) (hopen : IsOpen (I.support : Set X)) :
    ∃ K : ℕ, ∀ l, K ≤ l → I ^ (l + 1) = I ^ (K + 1) := by
  obtain ⟨K, hK⟩ := exists_pow_succ_eq I hopen
  exact ⟨K, powers_stable_of_succ_eq I K hK⟩

end FLT.Mazur.IdealSheafClopenStabilization

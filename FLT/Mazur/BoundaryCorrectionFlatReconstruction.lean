/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionLinearSystem
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Finite original reconstruction of a flat ambient correction

A solution after flat extension of the original scalar ring is a finite sum
of tensors of actual original solutions. No coefficient ring is assumed finite
over the scalar ring. Every summand retains one shared correction family for
all independent mixed equations.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j) (u : ∀ i, A i)
  (S : Type*) [CommRing S] [Algebra R S]

local notation "K" => correctionSolutions φ p q u
local notation "D" => correctionSystem φ p q u
set_option quotPrecheck false in
local notation "I" => ideal (fun i ↦ algebraMap R (A i))
  (fun i ↦ (φ i).toRingHom) (fun i j ↦ (p i j).toRingHom)
  (fun i j ↦ (q i j).toRingHom)
  (fun i j r ↦ Eq.trans ((p i j).commutes r) (Eq.symm ((q i j).commutes r))) u

/-- The original scalar coordinate of a tensor of correction pairs. -/
def tensorCorrectionMultiplier : (S ⊗[R] (R × ∀ i, A i)) →ₗ[R] S :=
  (TensorProduct.rid R S).toLinearMap.comp ((LinearMap.fst R R (∀ i, A i)).lTensor S)

/-- A pure tensor retains precisely its scalar multiplier. -/
theorem tensorCorrectionMultiplier_tmul (s : S) (x : R × ∀ i, A i) :
    tensorCorrectionMultiplier (A := A) S (s ⊗ₜ[R] x) = algebraMap R S x.1 * s := by
  simp only [tensorCorrectionMultiplier, LinearMap.comp_apply, LinearMap.lTensor_tmul,
    LinearMap.fst_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul, Algebra.smul_def]

/-- Any tensor of actual original solutions has multiplier in the extended original ideal. -/
theorem tensorCorrectionMultiplier_mem (y : S ⊗[R] K) :
    tensorCorrectionMultiplier (A := A) S ((K).subtype.lTensor S y) ∈
      (I).map (algebraMap R S) := by
  induction y using TensorProduct.inductionOn with
  | tmul s y =>
      rw [LinearMap.lTensor_tmul, tensorCorrectionMultiplier_tmul]
      exact Ideal.mul_mem_right s _
        (Ideal.mem_map_of_mem _ (correctionMultiplier_mem φ p q u y))
  | add x y hx hy =>
      simpa only [map_add] using ((I).map (algebraMap R S)).add_mem hx hy

variable [Module.Flat R S]

/-- Flatness reconstructs every full ambient solution from original simultaneous solutions. -/
theorem flatCorrection_exists_lift (x : S ⊗[R] (R × ∀ i, A i))
    (hx : (D).lTensor S x = 0) :
    ∃ y : S ⊗[R] K, (K).subtype.lTensor S y = x :=
  (Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map D) x).mp hx

/-- The reconstruction uses only finitely many original solutions, without module finiteness. -/
theorem flatCorrection_exists_finite (x : S ⊗[R] (R × ∀ i, A i))
    (hx : (D).lTensor S x = 0) :
    ∃ (n : ℕ) (s : Fin n → S) (y : Fin n → K),
      x = ∑ a, s a ⊗ₜ[R] (y a).val := by
  obtain ⟨v, hv⟩ := flatCorrection_exists_lift φ p q u S x hx
  obtain ⟨n, s, y, hy⟩ := TensorProduct.exists_sum_tmul_eq v
  refine ⟨n, s, y, ?_⟩
  rw [← hv, hy, map_sum]
  simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]

/-- The multiplier of an arbitrary flat ambient solution lies in the exact original ideal. -/
theorem flatCorrection_multiplier_mem (x : S ⊗[R] (R × ∀ i, A i))
    (hx : (D).lTensor S x = 0) :
    tensorCorrectionMultiplier (A := A) S x ∈ (I).map (algebraMap R S) := by
  obtain ⟨y, rfl⟩ := flatCorrection_exists_lift φ p q u S x hx
  exact tensorCorrectionMultiplier_mem φ p q u S y

end FLT.Mazur.BoundaryCorrectionIdeal

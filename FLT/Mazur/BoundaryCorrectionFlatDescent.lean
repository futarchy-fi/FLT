/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionFlatReconstruction
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Original nonvanishing scalars from flat ambient corrections

A full ambient correction whose multiplier avoids a test ideal produces an
actual original simultaneous solution whose scalar avoids its contraction.
Faithfully flat extension also detects exact ideal membership. Neither result
asserts that an ambient solution exists at an original boundary point.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j) (u : ∀ i, A i)
  (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S]

local notation "K" => correctionSolutions φ p q u
local notation "D" => correctionSystem φ p q u
set_option quotPrecheck false in
local notation "I" => ideal (fun i ↦ algebraMap R (A i))
  (fun i ↦ (φ i).toRingHom) (fun i j ↦ (p i j).toRingHom)
  (fun i j ↦ (q i j).toRingHom)
  (fun i j r ↦ Eq.trans ((p i j).commutes r) (Eq.symm ((q i j).commutes r))) u

/-- Flat ambient nonvanishing produces a nonvanishing scalar in the exact original ideal. -/
theorem flatCorrection_exists_scalar (P : Ideal S) (x : S ⊗[R] (R × ∀ i, A i))
    (hx : (D).lTensor S x = 0) (hn : tensorCorrectionMultiplier (A := A) S x ∉ P) :
    ∃ r : R, r ∈ I ∧ algebraMap R S r ∉ P := by
  have hm := flatCorrection_multiplier_mem φ p q u S x hx
  by_contra h
  push Not at h
  exact hn ((Ideal.map_le_iff_le_comap.mpr (show I ≤ P.comap (algebraMap R S) from h)) hm)

/-- The scalar comes with one actual shared correction family satisfying every original equation. -/
theorem flatCorrection_exists_nonvanishing_solution (P : Ideal S)
    (x : S ⊗[R] (R × ∀ i, A i)) (hx : (D).lTensor S x = 0)
    (hn : tensorCorrectionMultiplier (A := A) S x ∉ P) :
    ∃ y : K, algebraMap R S y.val.1 ∉ P := by
  obtain ⟨r, ⟨z, hz, he⟩, hr⟩ := flatCorrection_exists_scalar φ p q u S P x hx hn
  exact ⟨⟨(r, z), (mem_correctionSolutions φ p q u (r, z)).mpr ⟨hz, he⟩⟩, hr⟩

omit [Module.Flat R S] in
/-- An original multiplier always supplies a solution over every scalar extension. -/
theorem correction_exists_tensor_of_mem (r : R) (hr : r ∈ I) :
    ∃ x : S ⊗[R] (R × ∀ i, A i), (D).lTensor S x = 0 ∧
      tensorCorrectionMultiplier (A := A) S x = algebraMap R S r := by
  obtain ⟨z, hz, he⟩ := hr
  have hy : (r, z) ∈ K := (mem_correctionSolutions φ p q u (r, z)).mpr ⟨hz, he⟩
  refine ⟨1 ⊗ₜ[R] (r, z), ?_, ?_⟩
  · rw [LinearMap.lTensor_tmul, LinearMap.mem_ker.mp hy, TensorProduct.tmul_zero]
  · rw [tensorCorrectionMultiplier_tmul, mul_one]

omit [Module.Flat R S]
variable [Module.FaithfullyFlat R S]

/-- Faithfully flat ambient solutions detect membership in the unchanged original ideal. -/
theorem correction_mem_iff_faithfullyFlat (r : R) :
    r ∈ I ↔ ∃ x : S ⊗[R] (R × ∀ i, A i), (D).lTensor S x = 0 ∧
      tensorCorrectionMultiplier (A := A) S x = algebraMap R S r := by
  constructor
  · exact correction_exists_tensor_of_mem φ p q u S r
  · rintro ⟨x, hx, hr⟩
    have hm := flatCorrection_multiplier_mem φ p q u S x hx
    rw [hr] at hm
    have he := Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) I
    exact he ▸ (show r ∈ ((I).map (algebraMap R S)).comap (algebraMap R S) from hm)

end FLT.Mazur.BoundaryCorrectionIdeal

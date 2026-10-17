/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionAdicAmbient

/-!
# Finite original coefficient identities from uniformly finite ambient errors

One fixed finite error module at every order produces a finite sum of actual
original correction scalars congruent to one. Any source test killing the error
ideal therefore receives a genuine unit-ideal certificate.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
open FiniteErrorLinearLifting
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j) (u : ∀ i, A i)
  (S : Type*) [CommRing S] [Algebra R S]

variable [IsNoetherianRing S]
  (J : Ideal S) (E : Submodule S (S ⊗[R] ((∀ i, B i) × ∀ i j, C i j)))
  (hE : E.FG)
  (h : ∀ n : ℕ, ∃ z : S ⊗[R] (∀ i, A i),
    (correctionSystem φ p q u).baseChange S (tensorPair S (1, z)) ∈ J ^ n • E)
include hE h

variable [Module.Flat R S]

/-- A finite family of original shared solutions gives a scalar identity modulo the error ideal. -/
theorem adicAmbientCorrection_finite_congr :
    ∃ (n : ℕ) (a : Fin n → S) (y : Fin n → correctionSolutions φ p q u),
      (∑ k, algebraMap R S (y k).val.1 * a k) - 1 ∈ J := by
  obtain ⟨s, z, hs, hz⟩ :=
    exists_tensor_pair S (correctionSystem φ p q u) J E hE h
  obtain ⟨n, a, y, hy⟩ := flatCorrection_exists_finite φ p q u S (tensorPair S (s, z)) hz
  have hc := congrArg (tensorCorrectionMultiplier (A := A) S) hy
  rw [tensorPair_correctionMultiplier, map_sum] at hc
  simp only [tensorCorrectionMultiplier_tmul] at hc
  exact ⟨n, a, y, hc ▸ hs⟩

set_option quotPrecheck false in
local notation "I" => ideal (fun i ↦ algebraMap R (A i))
  (fun i ↦ (φ i).toRingHom) (fun i j ↦ (p i j).toRingHom)
  (fun i j ↦ (q i j).toRingHom)
  (fun i j r ↦ Eq.trans ((p i j).commutes r) (Eq.symm ((q i j).commutes r))) u

/-- Killing the error ideal turns the finite congruence into a source unit-ideal certificate. -/
theorem adicAmbientCorrection_map_eq_top {T : Type*} [CommRing T]
    (ρ : S →+* T) (hJ : J ≤ RingHom.ker ρ) :
    (I).map (ρ.comp (algebraMap R S)) = ⊤ := by
  obtain ⟨n, a, y, hy⟩ := adicAmbientCorrection_finite_congr φ p q u S J E hE h
  have he : ρ (∑ k, algebraMap R S (y k).val.1 * a k) = 1 := by
    apply sub_eq_zero.mp
    simpa only [RingHom.mem_ker, map_sub, map_one] using hJ hy
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← he, map_sum]
  apply Ideal.sum_mem
  intro k _
  rw [map_mul]
  apply Ideal.mul_mem_right
  exact Ideal.mem_map_of_mem _ (correctionMultiplier_mem φ p q u (y k))

end FLT.Mazur.BoundaryCorrectionIdeal

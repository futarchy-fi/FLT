/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionFiniteReduction

/-!
# Original finite certificates constructed from finite error reductions

The exact ambient correction reconstructs into a finite family of original
solutions. A source test killing the matrix ideal turns the scalar congruence
into the original source unit-ideal certificate. No Noetherianity is needed.
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
  (J : Ideal S) {κ : Type*} [Fintype κ]
  (e : κ → S ⊗[R] ((∀ i, B i) × ∀ i j, C i j))
  (v : κ → S ⊗[R] (∀ i, A i)) (c : κ → κ → S)
  (hc : ∀ j k, c j k ∈ J)
  (he : ∀ j, e j - (correctionSystem φ p q u).baseChange S (tensorPair S (0, v j)) =
    ∑ k, c j k • e k)
  (z₀ : S ⊗[R] (∀ i, A i)) (b : κ → S)
  (h₀ : (correctionSystem φ p q u).baseChange S (tensorPair S (1, z₀)) =
    ∑ j, b j • e j)
include hc he h₀

variable [Module.Flat R S]

/-- Finite reductions reconstruct finitely many original scalars with sum congruent to one. -/
theorem finiteReduction_finite_congr :
    ∃ (n : ℕ) (a : Fin n → S) (y : Fin n → correctionSolutions φ p q u),
      (∑ k, algebraMap R S (y k).val.1 * a k) - 1 ∈ J := by
  obtain ⟨x, hx, hs⟩ := finiteReduction_ambient φ p q u S J e v c hc he z₀ b h₀
  obtain ⟨n, a, y, hy⟩ := flatCorrection_exists_finite φ p q u S x hx
  have hsum := congrArg (tensorCorrectionMultiplier (A := A) S) hy
  rw [map_sum] at hsum
  simp only [tensorCorrectionMultiplier_tmul] at hsum
  exact ⟨n, a, y, hsum ▸ hs⟩

set_option quotPrecheck false in
local notation "I" => ideal (fun i ↦ algebraMap R (A i))
  (fun i ↦ (φ i).toRingHom) (fun i j ↦ (p i j).toRingHom)
  (fun i j ↦ (q i j).toRingHom)
  (fun i j r ↦ Eq.trans ((p i j).commutes r) (Eq.symm ((q i j).commutes r))) u

/-- A source test killing the reduction ideal receives an actual original unit-ideal witness. -/
theorem finiteReduction_map_eq_top {T : Type*} [CommRing T]
    (ρ : S →+* T) (hJ : J ≤ RingHom.ker ρ) :
    (I).map (ρ.comp (algebraMap R S)) = ⊤ := by
  obtain ⟨n, a, y, hy⟩ := finiteReduction_finite_congr φ p q u S J e v c hc he z₀ b h₀
  have heq : ρ (∑ k, algebraMap R S (y k).val.1 * a k) = 1 := by
    apply sub_eq_zero.mp
    simpa only [RingHom.mem_ker, map_sub, map_one] using hJ hy
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← heq, map_sum]
  apply Ideal.sum_mem
  intro k _
  rw [map_mul]
  apply Ideal.mul_mem_right
  exact Ideal.mem_map_of_mem _ (correctionMultiplier_mem φ p q u (y k))

end FLT.Mazur.BoundaryCorrectionIdeal

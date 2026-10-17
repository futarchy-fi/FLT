/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionLinearSystem
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Compatible errors from the exact mixed boundary ideals

The mixed error module keeps every independent mixed equation and has zero
boundary coordinate. Adjoining the correction image gives an explicit error
subspace containing the scalar obstruction whenever the chosen lifts agree on
the mixed boundary. No finite generation or residual surjectivity is asserted.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j) (u : ∀ i, A i)
  (J : ∀ i j, Ideal (C i j))

/-- Errors vanish in every boundary coordinate and belong to every exact mixed ideal. -/
def mixedBoundaryErrors : Submodule R ((∀ i, B i) × ∀ i j, C i j) where
  carrier := {x | x.1 = 0 ∧ ∀ i j, x.2 i j ∈ J i j}
  zero_mem' := ⟨rfl, fun i j ↦ (J i j).zero_mem⟩
  add_mem' hx hy := ⟨by simp only [Prod.fst_add, hx.1, hy.1, add_zero],
    fun i j ↦ (J i j).add_mem (hx.2 i j) (hy.2 i j)⟩
  smul_mem' r x hx := by
    refine ⟨?_, fun i j ↦ ?_⟩
    · change r • x.1 = 0
      rw [hx.1, smul_zero]
    · change r • x.2 i j ∈ J i j
      rw [Algebra.smul_def]
      exact (J i j).mul_mem_left _ (hx.2 i j)

/-- This membership test retains the exact ideals, including their nilpotents. -/
theorem mem_mixedBoundaryErrors (x : (∀ i, B i) × ∀ i j, C i j) :
    x ∈ mixedBoundaryErrors (R := R) (B := B) J ↔
      x.1 = 0 ∧ ∀ i j, x.2 i j ∈ J i j := Iff.rfl

/-- The original correction-only map, before any scalar extension. -/
def originalCorrectionOperator : (∀ i, A i) →ₗ[R] ((∀ i, B i) × ∀ i j, C i j) :=
  (correctionSystem φ p q u).comp (LinearMap.inr R R (∀ i, A i))

/-- Compatible errors together with the entire correction image. -/
def compatibleErrorSubspace : Submodule R ((∀ i, B i) × ∀ i j, C i j) :=
  LinearMap.range (originalCorrectionOperator φ p q u) ⊔ mixedBoundaryErrors J

/-- Every full correction vector lies in the constructed compatible error subspace. -/
theorem correction_range_le_compatible :
    LinearMap.range (originalCorrectionOperator φ p q u) ≤
      compatibleErrorSubspace φ p q u J := le_sup_left

/-- The scalar-one error is an actual mixed boundary error. -/
theorem scalarError_mem_mixedBoundaryErrors
    (hu : ∀ i j, p i j (u i) - q i j (u j) ∈ J i j) :
    correctionSystem φ p q u (1, 0) ∈ mixedBoundaryErrors (R := R) (B := B) J := by
  constructor
  · funext i
    exact map_zero (φ i)
  · intro i j
    change p i j 0 - q i j 0 - p i j (algebraMap R (A i) 1) *
      (p i j (u i) - q i j (u j)) ∈ J i j
    simpa only [map_zero, map_one, sub_self, one_mul, zero_sub] using
      (J i j).neg_mem (hu i j)

/-- In particular the actual scalar error belongs to the constructed compatible subspace. -/
theorem scalarError_mem_compatible
    (hu : ∀ i j, p i j (u i) - q i j (u j) ∈ J i j) :
    correctionSystem φ p q u (1, 0) ∈ compatibleErrorSubspace φ p q u J :=
  Submodule.mem_sup_right (scalarError_mem_mixedBoundaryErrors φ p q u J hu)

/-- Taking the cokernel removes the adjoined correction image and keeps precisely the errors. -/
theorem compatibleErrorSubspace_map_cokernel :
    (compatibleErrorSubspace φ p q u J).map
        (LinearMap.range (originalCorrectionOperator φ p q u)).mkQ =
      (mixedBoundaryErrors (R := R) (B := B) J).map
        (LinearMap.range (originalCorrectionOperator φ p q u)).mkQ := by
  rw [compatibleErrorSubspace, Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]

end FLT.Mazur.BoundaryCorrectionIdeal

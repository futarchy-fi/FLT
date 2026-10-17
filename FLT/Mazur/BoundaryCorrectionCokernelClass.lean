/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionOperatorIndependence

/-!
# Boundary representatives of the full scalar obstruction

Adding the correction of the chosen lifts to the scalar error leaves exactly
its boundary coordinates and zero mixed coordinates. Thus its full cokernel
class depends only on the boundary values, not on the chosen lifts. Every
independent mixed equation remains in the target and in the correction image.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j)
  (u v : ∀ i, A i)

/-- A full correction of the chosen lifts cancels precisely the mixed scalar error. -/
theorem scalarError_add_correction :
    correctionSystem φ p q u (1, 0) + originalCorrectionOperator φ p q v u =
      (fun i ↦ φ i (u i), 0) := by
  rw [originalCorrectionOperator_apply]
  apply Prod.ext
  · funext i
    change φ i 0 + φ i (u i) = _
    rw [map_zero, zero_add]
  · funext i j
    change (p i j 0 - q i j 0 - p i j (algebraMap R (A i) 1) *
      (p i j (u i) - q i j (u j))) + (p i j (u i) - q i j (u j)) = 0
    simp only [map_zero, map_one, sub_self, one_mul, zero_sub, neg_add_cancel]

/-- In the full original cokernel, the scalar error has a boundary-only representative. -/
theorem scalarError_cokernel_eq_boundary :
    (LinearMap.range (originalCorrectionOperator φ p q v)).mkQ
        (correctionSystem φ p q u (1, 0)) =
      (LinearMap.range (originalCorrectionOperator φ p q v)).mkQ
        (fun i ↦ φ i (u i), 0) := by
  rw [← scalarError_add_correction φ p q u v, map_add]
  have h : (LinearMap.range (originalCorrectionOperator φ p q v)).mkQ
      (originalCorrectionOperator φ p q v u) = 0 :=
    Submodule.Quotient.mk_eq_zero _ |>.mpr (LinearMap.mem_range_self _ u)
  rw [h, add_zero]

variable (S : Type*) [CommRing S] [Algebra R S]
set_option quotPrecheck false
local notation "F" => ambientCorrectionOperator φ p q v S

/-- Scalar extension preserves the full cancellation identity without a flatness hypothesis. -/
theorem ambientScalarError_add_correction :
    ambientScalarError φ p q u S + F (1 ⊗ₜ[R] u) =
      1 ⊗ₜ[R] (fun i ↦ φ i (u i), 0) := by
  rw [ambientScalarError_eq_tmul, ambientCorrectionOperator_eq_baseChange,
    LinearMap.baseChange_tmul, ← tmul_add, scalarError_add_correction]

/-- The extended scalar class is the class of the exact boundary values and zero mixed values. -/
theorem ambientScalarError_cokernel_eq_boundary :
    (LinearMap.range F).mkQ (ambientScalarError φ p q u S) =
      (LinearMap.range F).mkQ (1 ⊗ₜ[R] (fun i ↦ φ i (u i), 0)) := by
  rw [← ambientScalarError_add_correction φ p q u v S, map_add]
  have h : (LinearMap.range F).mkQ (F (1 ⊗ₜ[R] u)) = 0 :=
    Submodule.Quotient.mk_eq_zero _ |>.mpr (LinearMap.mem_range_self _ _)
  rw [h, add_zero]

/-- Different lifts of the same exact boundary section give the same full obstruction class. -/
theorem ambientScalarError_cokernel_independent (w : ∀ i, A i)
    (h : ∀ i, φ i (u i) = φ i (w i)) :
    (LinearMap.range F).mkQ (ambientScalarError φ p q u S) =
      (LinearMap.range F).mkQ (ambientScalarError φ p q w S) := by
  rw [ambientScalarError_cokernel_eq_boundary, ambientScalarError_cokernel_eq_boundary]
  exact congrArg (fun b ↦ (LinearMap.range F).mkQ (1 ⊗ₜ[R] (b, 0))) (funext h)

end FLT.Mazur.BoundaryCorrectionIdeal

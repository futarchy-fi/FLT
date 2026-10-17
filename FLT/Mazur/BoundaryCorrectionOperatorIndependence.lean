/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionCompatibleErrors
public import FLT.Mazur.BoundaryCorrectionFiniteCokernel

/-!
# The correction operator is independent of the chosen section

The operator and compatible error subspace can be fixed once for an atlas.
Only the scalar obstruction changes with the lifted boundary section. The
ambient correction operator is exactly the scalar extension of this fixed map.
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

/-- Setting the scalar to zero removes all dependence on the chosen chart lifts. -/
theorem originalCorrectionOperator_apply (z : ∀ i, A i) :
    originalCorrectionOperator φ p q u z =
      (fun i ↦ φ i (z i), fun i j ↦ p i j (z i) - q i j (z j)) := by
  apply Prod.ext
  · rfl
  · funext i j
    change _ - p i j (algebraMap R (A i) 0) * _ = _
    rw [map_zero, map_zero, zero_mul, sub_zero]
    rfl

/-- A single original correction operator serves every boundary section. -/
theorem originalCorrectionOperator_independent :
    originalCorrectionOperator φ p q u = originalCorrectionOperator φ p q v := by
  apply LinearMap.ext
  intro z
  rw [originalCorrectionOperator_apply, originalCorrectionOperator_apply]

/-- The compatible subspace also depends only on the atlas and its exact mixed boundary ideals. -/
theorem compatibleErrorSubspace_independent (J : ∀ i j, Ideal (C i j)) :
    compatibleErrorSubspace φ p q u J = compatibleErrorSubspace φ p q v J := by
  rw [compatibleErrorSubspace, compatibleErrorSubspace,
    originalCorrectionOperator_independent φ p q u v]

variable (S : Type*) [CommRing S] [Algebra R S]

/-- The ambient operator is literally the scalar extension of the original correction map. -/
theorem ambientCorrectionOperator_eq_baseChange :
    ambientCorrectionOperator φ p q u S = (originalCorrectionOperator φ p q u).baseChange S := by
  apply LinearMap.ext
  intro z
  change (correctionSystem φ p q u).baseChange S
    (FiniteErrorLinearLifting.tensorPair S (0, z)) = _
  rw [FiniteErrorLinearLifting.tensorPair_apply, zero_tmul, zero_add]
  change ((correctionSystem φ p q u).baseChange S).comp
    ((LinearMap.inr R R (∀ i, A i)).baseChange S) z = _
  rw [← LinearMap.baseChange_comp]
  rfl

/-- The ambient scalar error is the pure tensor of the original scalar error. -/
theorem ambientScalarError_eq_tmul :
    ambientScalarError φ p q u S = 1 ⊗ₜ[R] correctionSystem φ p q u (1, 0) := by
  rw [ambientScalarError, FiniteErrorLinearLifting.tensorPair_apply, map_zero, add_zero,
    LinearMap.baseChange_tmul]

/-- The full ambient correction image is the same for every choice of lifted section. -/
theorem ambientCorrectionOperator_independent :
    ambientCorrectionOperator φ p q u S = ambientCorrectionOperator φ p q v S := by
  rw [ambientCorrectionOperator_eq_baseChange, ambientCorrectionOperator_eq_baseChange,
    originalCorrectionOperator_independent φ p q u v]

end FLT.Mazur.BoundaryCorrectionIdeal

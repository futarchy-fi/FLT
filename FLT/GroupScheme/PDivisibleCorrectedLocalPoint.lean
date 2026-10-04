/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleOverlapCorrection

/-! # Corrected local points satisfy descent and retain the prescribed reduction -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C D : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
  [Algebra B D] [Algebra R D] [IsScalarTower R B D] [Module.FaithfullyFlat B D]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- Correct the actual local lift with equal overlap pullbacks and unchanged reduction. -/
theorem exists_corrected_local_point
    (hq : Function.Surjective (algebraMap B C))
    (hJ : RingHom.ker (algebraMap B C) ^ 2 = ⊥) (n : ℕ)
    (x : (X.level n).CoordinateRing →ₐ[R] C) (y : (X.level n).CoordinateRing →ₐ[R] D)
    (hy : (coverPointReduction (R := R) (B := B) (C := C) (D := D)).comp y =
      (Algebra.TensorProduct.includeRight.restrictScalars R).comp x) :
    ∃ z : (X.level n).CoordinateRing →ₐ[R] D,
      (∀ a, z a ⊗ₜ[B] (1 : D) = (1 : D) ⊗ₜ[B] z a) ∧
      (coverPointReduction (R := R) (B := B) (C := C) (D := D)).comp z =
        (Algebra.TensorProduct.includeRight.restrictScalars R).comp x := by
  obtain ⟨c, hc⟩ := X.exists_cover_discrepancy_correction hq hJ n x y hy
  let z := HopfAlgebra.pointDifference c.val y
  refine ⟨z, ?_, ?_⟩
  · have he := HopfAlgebra.pointDifference_corrected_eq _ _ _ _ hc
    intro a
    have hl := AlgHom.congr_fun (HopfAlgebra.pointDifference_postcomp
      ((Algebra.TensorProduct.includeLeft : D →ₐ[B] D ⊗[B] D).restrictScalars R) c.val y) a
    have hr := AlgHom.congr_fun (HopfAlgebra.pointDifference_postcomp
      ((Algebra.TensorProduct.includeRight : D →ₐ[B] D ⊗[B] D).restrictScalars R) c.val y) a
    exact hl.trans ((AlgHom.congr_fun he a).trans hr.symm)
  · change (coverPointReduction (R := R) (B := B) (C := C) (D := D)).comp
      (HopfAlgebra.pointDifference c.val y) = _
    rw [HopfAlgebra.pointDifference_postcomp, c.property,
      HopfAlgebra.pointDifference_augmentation_left, hy]

end ThreeAdicPlan.PDivisibleSystem

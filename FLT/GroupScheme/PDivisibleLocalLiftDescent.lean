/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCorrectedLocalPoint
public import FLT.GroupScheme.FaithfullyFlatPointDescent

/-! # Descent of corrected actual local lifts -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C D : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
  [Algebra B D] [Algebra R D] [IsScalarTower R B D] [Module.FaithfullyFlat B D]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- Correcting and descending a local point produces an actual lift over the original base. -/
theorem exists_point_lift_of_flat_cover
    (hq : Function.Surjective (algebraMap B C))
    (hJ : RingHom.ker (algebraMap B C) ^ 2 = ⊥) (n : ℕ)
    (x : (X.level n).CoordinateRing →ₐ[R] C) (y : (X.level n).CoordinateRing →ₐ[R] D)
    (hy : (coverPointReduction (R := R) (B := B) (C := C) (D := D)).comp y =
      (Algebra.TensorProduct.includeRight.restrictScalars R).comp x) :
    ∃ z : (X.level n).CoordinateRing →ₐ[R] B,
      (IsScalarTower.toAlgHom R B C).comp z = x := by
  obtain ⟨w, hw, hred⟩ := X.exists_corrected_local_point hq hJ n x y hy
  obtain ⟨z, hz, _⟩ := Algebra.existsUnique_point_of_faithfullyFlat w hw
  refine ⟨z, Algebra.point_descent_reduction (IsScalarTower.toAlgHom R B C)
    (coverPointReduction (R := R) (B := B) (C := C) (D := D))
    (Algebra.TensorProduct.includeRight.restrictScalars R)
    (Module.FaithfullyFlat.tensorProduct_mk_injective (A := B) (B := D) C) ?_ z w x hz hred⟩
  ext b
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul b

end ThreeAdicPlan.PDivisibleSystem

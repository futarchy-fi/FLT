/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleSystem

/-! # Division points over an actual faithfully flat cover of the test algebra

This constructs the cover over C. It does not lift that cover across a thickening B → C.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace AlgHom
variable {R A H C : Type} [CommRing R] [CommRing A] [CommRing H] [CommRing C]
  [Algebra R A] [Algebra R H] [Algebra R C]

/-- Pulling a faithfully flat affine map back along an actual point gives a cover with a lift. -/
theorem exists_faithfullyFlat_point_cover (f : A →ₐ[R] H)
    (hf : f.toRingHom.FaithfullyFlat) (x : A →ₐ[R] C) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra R D) (j : C →ₐ[R] D),
      j.toRingHom.FaithfullyFlat ∧ ∃ y : H →ₐ[R] D, y.comp f = j.comp x := by
  let : Algebra A H := f.toRingHom.toAlgebra
  let : Algebra A C := x.toRingHom.toAlgebra
  let : IsScalarTower R A H := IsScalarTower.of_algHom f
  let : IsScalarTower R A C := IsScalarTower.of_algHom x
  let : Module.FaithfullyFlat A H := hf
  let D := C ⊗[A] H
  let j : C →ₐ[R] D := IsScalarTower.toAlgHom R C D
  let y : H →ₐ[R] D := (Algebra.TensorProduct.includeRight : H →ₐ[A] D).restrictScalars R
  refine ⟨D, inferInstance, inferInstance, j, ?_, y, ?_⟩
  · change (algebraMap C D).FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  · ext a
    change (1 : C) ⊗ₜ[A] f a = x a ⊗ₜ[A] (1 : H)
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul a).symm

end AlgHom

namespace ThreeAdicPlan.PDivisibleSystem
variable {R K C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing C] [Algebra R C]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- The original reduction admits a division point over a faithfully flat cover of C. -/
theorem exists_reduction_point_cover {n m : ℕ} (h : n ≤ m)
    (x : (X.level n).CoordinateRing →ₐ[R] C) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra R D) (j : C →ₐ[R] D),
      j.toRingHom.FaithfullyFlat ∧
        ∃ y : (X.level m).CoordinateRing →ₐ[R] D,
          y.comp (X.reduction h).toAlgHom = j.comp x :=
  AlgHom.exists_faithfullyFlat_point_cover (X.reduction h).toAlgHom (X.faithfullyFlat h) x

end ThreeAdicPlan.PDivisibleSystem

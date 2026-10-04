/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleDivisionCover
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # The specified division point on each principal pullback chart -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace AlgHom
variable {R A H C : Type*} [CommRing R] [CommRing A] [CommRing H] [CommRing C]
  [Algebra R A] [Algebra R H] [Algebra R C]
  [Algebra A H] [Algebra A C] [IsScalarTower R A H] [IsScalarTower R A C]

/-- The tensor pullback point restricts to every specified principal chart, with its
original coordinate composite. No choice of another division point is made. -/
theorem principal_pullback_point_comp (s : C ⊗[A] H) :
    ((IsScalarTower.toAlgHom R (C ⊗[A] H) (Localization.Away s)).comp
      (Algebra.TensorProduct.includeRight.restrictScalars R)).comp
        (IsScalarTower.toAlgHom R A H) =
      (IsScalarTower.toAlgHom R C (Localization.Away s)).comp
        (IsScalarTower.toAlgHom R A C) := by
  ext a
  change algebraMap _ (Localization.Away s) ((1 : C) ⊗ₜ[A] algebraMap A H a) = _
  rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rfl

end AlgHom

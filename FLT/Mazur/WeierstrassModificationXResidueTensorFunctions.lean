/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXResidueContraction

/-!
# Pure tensors and depth-sensitive contraction functions

Scalar multiples of every original chart function pass through the existing
residue equivalence. The original scale relation survives as t*x=0. The
strict-depth x formula loses precisely the vanishing constant coefficient;
at middle depth that coefficient remains a unit.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)

local notation "K" => ResidueField R
local notation "F" => FiberCoordinate (residue R W.a₁) (residue R b6)
local notation "f" => residueNormalMap D k hk0 hk b3 b4 b6 h3 h4

/-- Every original pure tensor is transported by the same existing residue equivalence. -/
theorem residueFiberEquiv_tmul (r : K) (z : Coordinate W (π ^ k) b3 b4 b6) :
    residueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4 (r ⊗ₜ[R] z) = r • f z := by
  rw [residueNormalMap_apply, ← map_smul]
  congr 1
  change (r ⊗ₜ[R] z : K ⊗[R] _) = r • ((1 : K) ⊗ₜ[R] z)
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The original scale becomes exactly the zero incidence equation in the tensor fiber. -/
theorem residueNormalMap_incidence :
    f (t W (π ^ k) b3 b4 b6) * f (x W (π ^ k) b3 b4 b6) = 0 := by
  rw [← map_mul, incidence, AlgHom.commutes,
    IsScalarTower.algebraMap_apply R K F, ResidueField.algebraMap_eq,
    WeierstrassDilatation.residue_scale_eq_zero D k hk0, map_zero]

/-- Wherever the actual tensor incidence coordinate is a unit, the original x vanishes. -/
theorem residueNormalMap_x_eq_zero_of_isUnit_t
    (ht : IsUnit (f (t W (π ^ k) b3 b4 b6))) :
    f (x W (π ^ k) b3 b4 b6) = 0 := by
  exact ht.mul_left_cancel (by
    rw [mul_zero]
    exact residueNormalMap_incidence D k hk0 hk b3 b4 b6 h3 h4)

/-- The same actual locus contracts with original y=0 as well. -/
theorem residueNormalMap_y_eq_zero_of_isUnit_t
    (ht : IsUnit (f (t W (π ^ k) b3 b4 b6))) :
    f (y W (π ^ k) b3 b4 b6) = 0 := by
  rw [residueNormalMap_y,
    residueNormalMap_x_eq_zero_of_isUnit_t D k hk0 hk b3 b4 b6 h3 h4 ht, zero_mul]

variable (h6 : W.a₆ = (π ^ k) ^ 2 * b6)

include h6 in
/-- Before middle depth, exactly the constant-depth term vanishes. -/
theorem residueNormalMap_x_strict (hstrict : 2 * k < n) :
    f (x W (π ^ k) b3 b4 b6) =
      f (v W (π ^ k) b3 b4 b6) *
        (f (v W (π ^ k) b3 b4 b6) + algebraMap R F W.a₁) := by
  rw [residueNormalMap_x,
    residueNormal_coefficient_zero b6 b6
      (WeierstrassDilatation.divided_constant_mem D k hstrict b6 h6), zero_mul, sub_zero]

include h6 in
/-- The strict-depth vertical contraction is the same quadratic times the original slope. -/
theorem residueNormalMap_y_strict (hstrict : 2 * k < n) :
    f (y W (π ^ k) b3 b4 b6) =
      (f (v W (π ^ k) b3 b4 b6) *
        (f (v W (π ^ k) b3 b4 b6) + algebraMap R F W.a₁)) *
          f (v W (π ^ k) b3 b4 b6) := by
  rw [residueNormalMap_y, residueNormalMap_x_strict D k hk0 hk b3 b4 b6 h3 h4 h6 hstrict]

omit [IsDomain R] in
include D h6 in
/-- At middle depth the coefficient in the transported contraction is still a unit. -/
theorem residueNormal_constant_isUnit (hmiddle : 2 * k = n) :
    IsUnit (algebraMap R F b6) := by
  rw [IsScalarTower.algebraMap_apply R K F, ResidueField.algebraMap_eq]
  exact (residue_middle_constant_isUnit D k b6 h6 hmiddle).map (algebraMap K F)

end FLT.Mazur.WeierstrassModificationX

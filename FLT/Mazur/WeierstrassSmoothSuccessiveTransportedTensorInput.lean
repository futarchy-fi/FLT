/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothSuccessiveResidueInputs
public import FLT.Mazur.WeierstrassSmoothSuccessiveTensorInput

/-!
# Integral transport recovers the original successive tensor inputs

Specializing the actual integral incidence refinement and extending scalars
gives exactly the independently constructed original conic input maps.
The equalities retain every tensor function and both residue parameters.
-/

@[expose] public noncomputable section
open IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {k depth : ℕ}
  (d : WeierstrassDividedDepth.Data W π (k + 1)) (hπ : π ≠ 0)
  (D : SplitNodeDepth W π depth) (hk0 : 0 < k) (hk : 2 * (k + 1) < depth)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "A" => WeierstrassSuccessiveX.Coordinate W (π ^ k) π d.b3 d.b4 d.b6
local notation "B" => ScalarExtension W (π ^ k) π d.b3 d.b4 d.b6 K

/-- Extend the actual transported first input over the original residue field. -/
def smoothSuccessiveFirstTransportedTensorInput : B →ₐ[K] C :=
  AlgHom.liftEquiv R K A C (smoothSuccessiveFirstResidueInput d hπ D (Nat.zero_lt_succ k) hk)

/-- The complete transported first tensor input is the original independent conic input. -/
theorem smoothSuccessiveFirstTransportedTensorInput_eq :
    smoothSuccessiveFirstTransportedTensorInput d hπ D hk =
      smoothSuccessiveFirstTensorInput D d hk0 hk := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassSuccessiveX.hom_ext
  intro i
  simp only [smoothSuccessiveFirstTransportedTensorInput, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
    AlgHom.liftEquiv_tmul, one_smul]
  change smoothSuccessiveFirstResidueInput d hπ D (Nat.zero_lt_succ k) hk
    (WeierstrassSuccessiveX.coord W (π ^ k) π d.b3 d.b4 d.b6 i) =
      smoothSuccessiveFirstTensorInput D d hk0 hk
        (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K i)
  fin_cases i
  · erw [smoothSuccessiveFirstResidueInput_t, smoothSuccessiveFirstTensorInput_t]
  · erw [smoothSuccessiveFirstResidueInput_v, smoothSuccessiveFirstTensorInput_v]
  · erw [smoothSuccessiveFirstResidueInput_u, smoothSuccessiveFirstTensorInput_u]

/-- Extend the actual transported second input over the original residue field. -/
def smoothSuccessiveSecondTransportedTensorInput : B →ₐ[K] C :=
  AlgHom.liftEquiv R K A C (smoothSuccessiveSecondResidueInput d hπ D (Nat.zero_lt_succ k) hk)

/-- The complete transported second tensor input is the original independent conic input. -/
theorem smoothSuccessiveSecondTransportedTensorInput_eq :
    smoothSuccessiveSecondTransportedTensorInput d hπ D hk =
      smoothSuccessiveSecondTensorInput D d hk0 hk := by
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassSuccessiveX.hom_ext
  intro i
  simp only [smoothSuccessiveSecondTransportedTensorInput, AlgHom.comp_apply,
    AlgHom.restrictScalars_apply, Algebra.TensorProduct.includeRight_apply,
    AlgHom.liftEquiv_tmul, one_smul]
  change smoothSuccessiveSecondResidueInput d hπ D (Nat.zero_lt_succ k) hk
    (WeierstrassSuccessiveX.coord W (π ^ k) π d.b3 d.b4 d.b6 i) =
      smoothSuccessiveSecondTensorInput D d hk0 hk
        (tensorCoord W (π ^ k) π d.b3 d.b4 d.b6 K i)
  fin_cases i
  · erw [smoothSuccessiveSecondResidueInput_t, smoothSuccessiveSecondTensorInput_t]
  · erw [smoothSuccessiveSecondResidueInput_v, smoothSuccessiveSecondTensorInput_v]
    rw [IsScalarTower.algebraMap_apply R K C, ResidueField.algebraMap_eq]
  · erw [smoothSuccessiveSecondResidueInput_u, smoothSuccessiveSecondTensorInput_u]

end FLT.Mazur.WeierstrassIntegralChart

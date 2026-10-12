/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRootShearZeroSmooth
public import FLT.Mazur.WeierstrassRootShearUnitAddition
public import FLT.Mazur.WeierstrassSmoothHorizontalResiduePoint

/-!
# The original horizontal smooth input has the positive root-shear parameter

The whole Laurent evaluation, including negative powers, agrees with the
independent smooth factor. This fixes the orientation used by both conic actions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R
local notation "V" => W.map (algebraMap R K)
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "L" => K[T;T⁻¹]
local notation "P" => SmoothYParameterRing D
local notation "τ" => smoothHorizontalTangentUnit D

/-- The split-depth hypotheses supply all zero-root nodal coefficient conditions. -/
theorem splitDepth_zeroRoot_conditions :
    (a : K) = (V).a₁ + 2 * 0 ∧ 0 ^ 2 + (V).a₁ * 0 - (V).a₂ = 0 ∧
      (V).a₃ = 0 ∧ (V).a₄ = 0 ∧ (V).a₆ = 0 := by
  rw [splitDepth_residue_equation D D.depth_pos]
  simp only [splitNodalEquation, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero, and_self]

omit [IsDomain R] in
/-- Evaluation at the tangent unit is the full independent smooth-factor algebra map. -/
theorem smoothHorizontalTangentUnit_evaluation :
    LaurentUnitPoints.evalUnit (R := K) τ =
      (smoothHorizontalResidueParameter D).comp (IsScalarTower.toAlgHom K L P) := by
  have h := LaurentUnitPoints.evalUnit_pointUnit
    ((smoothHorizontalResidueParameter D).comp (IsScalarTower.toAlgHom K L P))
  have hu : LaurentUnitPoints.pointUnit
      ((smoothHorizontalResidueParameter D).comp (IsScalarTower.toAlgHom K L P)) = τ := by
    apply Units.ext
    exact (smoothHorizontalTangentUnit_val D).symm
  rw [hu] at h
  exact h

local notation "hc" => splitDepth_zeroRoot_conditions D

/-- The actual root-sheared torus parameter has the positive, not reciprocal, tangent unit. -/
theorem smoothHorizontalResiduePoint_rootParameter :
    (rootShearSmoothUnitInput V 0 a (hc).1 (hc).2.1 (hc).2.2.1
      (hc).2.2.2.1 (hc).2.2.2.2 τ).left =
        smoothHorizontalResiduePoint D D.depth_pos := by
  rw [rootShearSmoothUnitInput_parameter,
    rootShearTorusSmoothIso_zero V a (splitDepth_residue_equation D D.depth_pos),
    smoothHorizontalTangentUnit_evaluation]
  change Spec.map _ ≫ (infinityResidueSmoothIso D D.depth_pos).hom = _
  rw [smoothHorizontalResiduePoint, ← Category.assoc, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassIntegralChart

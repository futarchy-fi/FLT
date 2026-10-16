/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeParameterScaling
public import FLT.Mazur.PolygonTopNodeReduction

/-!
# Full node defects of adjacent-stage branch scalings

The difference between the two original branch substitutions and node
scaling is a linear map on the whole original node. If the substitutions
restrict to scaling at the preceding stage, its values are square zero
and it kills the entire original closed-fiber kernel.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonChartScaling PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "B" => ChartRing (e)
local notation "L" => (S)[T;T⁻¹]
local notation "β" => stageNodeBranchPair R (m + 1)
variable (u v : ((Ring R (m + 1))[T;T⁻¹])ˣ) (a : (Ring R (m + 1))ˣ)
local notation "F" => stageNodeBranchSubstitution R (m + 1) u v
local notation "σ" => reciprocalScale (e) a

/-- The full original difference, before any node-preservation conclusion. -/
def topNodeActionDefect : (B) →ₗ[S] ((L) × (L)) :=
  ((F).comp (β)).toLinearMap - ((β).comp (σ)).toLinearMap

/-- The difference is computed in the two unchanged full Laurent rings. -/
theorem topNodeActionDefect_apply (z : B) :
    topNodeActionDefect R m u v a z = (F) ((β) z) - (β) ((σ) z) := rfl

local notation "D" => topNodeActionDefect R m u v a
variable
  (hu : coeffMap (restriction R m).toRingHom u.val = C (restriction R m a.val) * T 1)
  (hv : coeffMap (restriction R m).toRingHom v.val = C (restriction R m a⁻¹.val) * T 1)
include hu hv

/-- Every full defect is killed by the original smoothing parameter. -/
theorem topNodeActionDefect_parameter (z : B) : (e) • (D) z = 0 := by
  rw [← (D).map_smul, topNodeActionDefect_apply,
    topNodeBranchSubstitution_parameter_scaling R m u v a hu hv, sub_self]

/-- All products of full defects vanish, retaining every original coefficient. -/
theorem topNodeActionDefect_mul_zero (z w : B) : (D) z * (D) w = 0 :=
  topNodePair_annihilator_mul R m _ _
    (topNodeActionDefect_parameter R m u v a hu hv z)
    (topNodeActionDefect_parameter R m u v a hu hv w)

/-- The original defect satisfies the square-zero derivation rule on all node functions. -/
theorem topNodeActionDefect_mul (z w : B) :
    (D) (z * w) = (D) z * (β) ((σ) w) + (D) w * (β) ((σ) z) := by
  have hz := topNodeActionDefect_mul_zero R m u v a hu hv z w
  simp only [topNodeActionDefect_apply, map_mul] at hz ⊢
  linear_combination hz

/-- The entire original closed-fiber kernel is killed by the computed defect. -/
theorem topNodeActionDefect_kernel (z : B) (hz : topNodeReduction R m z = 0) :
    (D) z = 0 := by
  obtain ⟨w, rfl⟩ := (topNodeReduction_zero_iff R m z).mp hz
  rw [(D).map_smul]
  exact topNodeActionDefect_parameter R m u v a hu hv w

/-- Equal reduced node functions have the same full, unchanged branch defect. -/
theorem topNodeActionDefect_eq (z w : B)
    (hzw : topNodeReduction R m z = topNodeReduction R m w) : (D) z = (D) w := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply topNodeActionDefect_kernel R m u v a hu hv
  rw [(topNodeReduction R m).map_sub, hzw, sub_self]

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeTangentLift

/-!
# Actual inverses of the first-node extensions

Every endomorphism of the first smoothing node reducing to the identity
is an automorphism. Its inverse is the explicit function z ↦ z - (f z - z).
Thus the constructed tangent lifts are genuine coordinate changes on the
whole original node, including its nonreduced smoothing coefficient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)
local notation "N" => ChartRing (0 : R)
variable (f : ChartRing (parameter R 1) →ₐ[Ring R 1] ChartRing (parameter R 1))
  (hf : ∀ z, firstNodeReduction R (f z) = firstNodeReduction R z)

include hf

/-- Such an endomorphism fixes the entire parameter ideal pointwise. -/
theorem firstNodeEndomorphism_weighted (z : B) : f ((e) • z) = (e) • z := by
  have he : (e) • (f z - z) = 0 := by
    rw [firstNode_parameter_annihilator, (firstNodeReduction R).map_sub, hf, sub_self]
  rw [smul_sub, sub_eq_zero] at he
  exact (f.toLinearMap.map_smul (e) z).trans he

/-- The actual coordinate difference is fixed by the endomorphism. -/
theorem firstNodeEndomorphism_difference_fixed (z : B) : f (f z - z) = f z - z := by
  rw [← firstNodeDifference_spec R f hf z]
  exact firstNodeEndomorphism_weighted R f hf _

/-- Subtracting the actual coordinate difference is a right inverse on every function. -/
theorem firstNodeEndomorphism_inverse_right (z : B) : f (z - (f z - z)) = z := by
  rw [map_sub f, firstNodeEndomorphism_difference_fixed R f hf]
  abel

/-- The same explicit subtraction is a left inverse on every function. -/
theorem firstNodeEndomorphism_inverse_left (z : B) : f z - (f (f z) - f z) = z := by
  have he := firstNodeEndomorphism_difference_fixed R f hf z
  rw [map_sub f] at he
  rw [he]
  abel

/-- The original endomorphism, promoted to an actual algebra automorphism with explicit inverse. -/
def firstNodeEndomorphismEquiv : (B) ≃ₐ[S] (B) :=
  { f with
    invFun := fun z ↦ z - (f z - z)
    left_inv := firstNodeEndomorphism_inverse_left R f hf
    right_inv := firstNodeEndomorphism_inverse_right R f hf }

/-- The promotion retains the originally specified endomorphism exactly. -/
theorem firstNodeEndomorphismEquiv_apply (z : B) : firstNodeEndomorphismEquiv R f hf z = f z :=
  rfl

/-- The inverse is subtraction of the exact original coordinate difference. -/
theorem firstNodeEndomorphismEquiv_symm_apply (z : B) :
    (firstNodeEndomorphismEquiv R f hf).symm z = z - (f z - z) := rfl

/-- The inverse also reduces to the identity on the whole original split node. -/
theorem firstNodeEndomorphismEquiv_symm_reduction (z : B) :
    firstNodeReduction R ((firstNodeEndomorphismEquiv R f hf).symm z) =
      firstNodeReduction R z := by
  rw [firstNodeEndomorphismEquiv_symm_apply, (firstNodeReduction R).map_sub,
    (firstNodeReduction R).map_sub, hf, sub_self, sub_zero]

omit hf

/-- Every split-node derivation now constructs a genuine automorphism of the smoothing node. -/
def firstNodeTangentAutomorphism (d : Derivation R (N) (N)) : (B) ≃ₐ[S] (B) :=
  firstNodeEndomorphismEquiv R (firstNodeTangentLift R d) (firstNodeTangentLift_reduction R d)

/-- This coordinate change retains the full tangent lift, with no restriction of its domain. -/
theorem firstNodeTangentAutomorphism_apply (d : Derivation R (N) (N)) (z : B) :
    firstNodeTangentAutomorphism R d z = firstNodeTangentLift R d z := rfl

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeTangentLift

/-!
# Actual inverses of top-layer node extensions

Every endomorphism of the original smoothing node trivial at the preceding
stage is an automorphism. Subtracting its exact coordinate difference is
an explicit inverse on the whole node, retaining all nilpotent coefficients.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R] (m : ℕ)
local notation "S" => Ring R (m + 1)
local notation "e" => parameter R (m + 1)
local notation "B" => ChartRing (e)
local notation "N" => ChartRing (0 : R)
variable (f : ChartRing (parameter R (m + 1)) →ₐ[Ring R (m + 1)] ChartRing (parameter R (m + 1)))
  (hf : ∀ z, topNodeRestriction R m (f z) = topNodeRestriction R m z)

include hf

/-- Such an endomorphism fixes the entire top-power ideal pointwise. -/
theorem topNodeEndomorphism_weighted (z : B) : f ((e) ^ (m + 1) • z) = (e) ^ (m + 1) • z := by
  have he : (e) ^ (m + 1) • (f z - z) = 0 := by
    rw [← topNodeDifference_spec R m f hf, smul_smul]
    have he : (e) ^ (m + 1) * (e) ^ (m + 1) = 0 := by
      rw [← pow_two]
      simpa using parameter_top_weight_sq R m (S)
    rw [he, zero_smul]
  rw [smul_sub, sub_eq_zero] at he
  exact (f.toLinearMap.map_smul ((e) ^ (m + 1)) z).trans he

/-- The actual coordinate difference is fixed by the endomorphism. -/
theorem topNodeEndomorphism_difference_fixed (z : B) : f (f z - z) = f z - z := by
  rw [← topNodeDifference_spec R m f hf z]
  exact topNodeEndomorphism_weighted R m f hf _

/-- Subtracting the actual coordinate difference is a right inverse on every function. -/
theorem topNodeEndomorphism_inverse_right (z : B) : f (z - (f z - z)) = z := by
  rw [map_sub f, topNodeEndomorphism_difference_fixed R m f hf]
  abel

/-- The same explicit subtraction is a left inverse on every function. -/
theorem topNodeEndomorphism_inverse_left (z : B) : f z - (f (f z) - f z) = z := by
  have he := topNodeEndomorphism_difference_fixed R m f hf z
  rw [map_sub f] at he
  rw [he]
  abel

/-- The original endomorphism, promoted to an actual algebra automorphism with explicit inverse. -/
def topNodeEndomorphismEquiv : (B) ≃ₐ[S] (B) :=
  { f with
    invFun := fun z ↦ z - (f z - z)
    left_inv := topNodeEndomorphism_inverse_left R m f hf
    right_inv := topNodeEndomorphism_inverse_right R m f hf }

/-- The promotion retains the originally specified endomorphism exactly. -/
theorem topNodeEndomorphismEquiv_apply (z : B) : topNodeEndomorphismEquiv R m f hf z = f z :=
  rfl

/-- The inverse is subtraction of the exact original coordinate difference. -/
theorem topNodeEndomorphismEquiv_symm_apply (z : B) :
    (topNodeEndomorphismEquiv R m f hf).symm z = z - (f z - z) := rfl

/-- The inverse also reduces to the identity on the whole preceding-stage node. -/
theorem topNodeEndomorphismEquiv_symm_restriction (z : B) :
    topNodeRestriction R m ((topNodeEndomorphismEquiv R m f hf).symm z) =
      topNodeRestriction R m z := by
  rw [topNodeEndomorphismEquiv_symm_apply, (topNodeRestriction R m).map_sub,
    (topNodeRestriction R m).map_sub, hf, sub_self, sub_zero]

omit hf

/-- Every split-node derivation now constructs a genuine automorphism of the smoothing node. -/
def topNodeTangentAutomorphism (d : Derivation R (N) (N)) : (B) ≃ₐ[S] (B) :=
  topNodeEndomorphismEquiv R m (topNodeTangentLift R m d) (topNodeTangentLift_restriction R m d)

/-- This coordinate change retains the full tangent lift, with no restriction of its domain. -/
theorem topNodeTangentAutomorphism_apply (d : Derivation R (N) (N)) (z : B) :
    topNodeTangentAutomorphism R m d z = topNodeTangentLift R m d z := rfl

end FLT.Mazur.PolygonInfinitesimalStages

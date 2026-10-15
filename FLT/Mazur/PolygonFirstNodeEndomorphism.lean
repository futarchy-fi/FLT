/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeReduction
public import FLT.Mazur.PolygonSmoothingDerivation
public import FLT.Mazur.NodeDerivationBoundary

/-!
# Extracting a node vector field from an original first-order endomorphism

An endomorphism of the actual smoothing chart that reduces to the identity
has parameter-divisible coordinate differences. Their reductions satisfy
the split-node tangent equation, hence define a genuine node derivation.
No endomorphism extending the original group action is assumed to exist.
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
local notation "C₀" => ChartRing (0 : R)
variable (f : ChartRing (parameter R 1) →ₐ[Ring R 1] ChartRing (parameter R 1))
  (hf : ∀ z, firstNodeReduction R (f z) = firstNodeReduction R z)

/-- A coordinate difference has an actual lift after dividing by the smoothing parameter. -/
def firstNodeDifference (z : B) : B :=
  Classical.choose ((firstNodeReduction_zero_iff R (f z - z)).mp
    (by rw [(firstNodeReduction R).map_sub, hf, sub_self]))

/-- The selected difference retains the original endomorphism coordinate exactly. -/
theorem firstNodeDifference_spec (z : B) :
    (e) • firstNodeDifference R f hf z = f z - z :=
  Classical.choose_spec ((firstNodeReduction_zero_iff R (f z - z)).mp
    (by rw [(firstNodeReduction R).map_sub, hf, sub_self]))

/-- The reduced coordinate difference is independent of the selected parameter division. -/
theorem firstNodeDifference_reduction_unique (z a : B) (ha : (e) • a = f z - z) :
    firstNodeReduction R a = firstNodeReduction R (firstNodeDifference R f hf z) := by
  apply sub_eq_zero.mp
  rw [← (firstNodeReduction R).map_sub, ← firstNode_parameter_annihilator, smul_sub,
    ha, firstNodeDifference_spec, sub_self]

/-- Preserving xy = e forces the reduced coordinate differences to satisfy its tangent equation. -/
theorem firstNodeDifference_relation :
    leftCoordinate (0 : R) *
        firstNodeReduction R (firstNodeDifference R f hf (rightCoordinate (e))) +
      rightCoordinate (0 : R) *
        firstNodeReduction R (firstNodeDifference R f hf (leftCoordinate (e))) = 0 := by
  let x := leftCoordinate (e)
  let y := rightCoordinate (e)
  let a := firstNodeDifference R f hf x
  let b := firstNodeDifference R f hf y
  let t := algebraMap (S) (B) (e)
  have hx : f x = x + t * a := by
    have he : t * a = f x - x :=
      (Algebra.smul_def (e) a).symm.trans (firstNodeDifference_spec R f hf x)
    exact (sub_eq_iff_eq_add.mp he.symm).trans (add_comm _ _)
  have hy : f y = y + t * b := by
    have he : t * b = f y - y :=
      (Algebra.smul_def (e) b).symm.trans (firstNodeDifference_spec R f hf y)
    exact (sub_eq_iff_eq_add.mp he.symm).trans (add_comm _ _)
  have hp : (x + t * a) * (y + t * b) = t := by
    rw [← hx, ← hy, ← map_mul, coordinate_relation, f.commutes]
  have he : (e) • (x * b + y * a) = 0 := by
    apply (Algebra.smul_def (e) (x * b + y * a)).trans
    have hxy : x * y = t := coordinate_relation (e)
    have ht : t ^ 2 = 0 := firstNode_parameter_sq R
    linear_combination hp - hxy - a * b * ht
  have hr := (firstNode_parameter_annihilator R _).mp he
  simpa only [x, y, a, b, (firstNodeReduction R).map_add, (firstNodeReduction R).map_mul,
    firstNodeReduction_left, firstNodeReduction_right] using hr

/-- The actual reduced coordinate errors define a derivation on the original split-node quotient. -/
def firstNodeDifferenceDerivation : Derivation R (C₀) (C₀) :=
  derivationOfCoordinates (0 : R)
    (firstNodeReduction R (firstNodeDifference R f hf (leftCoordinate (e))))
    (firstNodeReduction R (firstNodeDifference R f hf (rightCoordinate (e))))
    (by simpa only [smul_eq_mul] using firstNodeDifference_relation R f hf)

/-- Transport the constructed vector field through the original node equalizer comparison. -/
def firstNodeEqualizerDerivation :
    Derivation R (PolygonNodeEqualizer.A (R := R)) (PolygonNodeEqualizer.A (R := R)) where
  toLinearMap := (specialFiberEquiv R).toLinearEquiv.toLinearMap.comp
    ((firstNodeDifferenceDerivation R f hf).toLinearMap.comp
      (specialFiberEquiv R).symm.toLinearEquiv.toLinearMap)
  map_one_eq_zero' := by simp
  leibniz' a b := by
    change specialFiberEquiv R (firstNodeDifferenceDerivation R f hf
      ((specialFiberEquiv R).symm (a * b))) =
        a * specialFiberEquiv R (firstNodeDifferenceDerivation R f hf
          ((specialFiberEquiv R).symm b)) +
        b * specialFiberEquiv R (firstNodeDifferenceDerivation R f hf
          ((specialFiberEquiv R).symm a))
    rw [map_mul (specialFiberEquiv R).symm a b,
      (firstNodeDifferenceDerivation R f hf).leibniz]
    simp only [smul_eq_mul, map_add (specialFiberEquiv R), map_mul (specialFiberEquiv R),
      (specialFiberEquiv R).apply_symm_apply]

end FLT.Mazur.PolygonInfinitesimalStages

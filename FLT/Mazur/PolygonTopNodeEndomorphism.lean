/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeReduction
public import FLT.Mazur.PolygonSmoothingDerivation
public import FLT.Mazur.NodeDerivationBoundary

/-!
# Node vector fields from endomorphisms trivial at the preceding stage

Divide the actual coordinate differences by the top parameter power.
Flatness makes their closed-fiber reductions independent of division,
and the unchanged node equation forces the split-node tangent relation.
This constructs a derivation on the original split-node quotient.
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
local notation "C₀" => ChartRing (0 : R)
variable (f : ChartRing (parameter R (m + 1)) →ₐ[Ring R (m + 1)] ChartRing (parameter R (m + 1)))
  (hf : ∀ z, topNodeRestriction R m (f z) = topNodeRestriction R m z)

/-- A coordinate difference has an actual lift after dividing by the top parameter power. -/
def topNodeDifference (z : B) : B :=
  Classical.choose ((topNodeRestriction_zero_iff R m (f z - z)).mp
    (by rw [(topNodeRestriction R m).map_sub, hf, sub_self]))

/-- The selected difference retains the original endomorphism coordinate exactly. -/
theorem topNodeDifference_spec (z : B) :
    (e) ^ (m + 1) • topNodeDifference R m f hf z = f z - z :=
  Classical.choose_spec ((topNodeRestriction_zero_iff R m (f z - z)).mp
    (by rw [(topNodeRestriction R m).map_sub, hf, sub_self]))

/-- The reduced coordinate difference is independent of the selected top-power division. -/
theorem topNodeDifference_reduction_unique (z a : B) (ha : (e) ^ (m + 1) • a = f z - z) :
    topNodeReduction R m a = topNodeReduction R m (topNodeDifference R m f hf z) := by
  apply sub_eq_zero.mp
  rw [← (topNodeReduction R m).map_sub, ← topNode_parameter_annihilator, smul_sub,
    ha, topNodeDifference_spec, sub_self]

/-- Preserving xy = e forces the reduced coordinate differences to satisfy its tangent equation. -/
theorem topNodeDifference_relation :
    leftCoordinate (0 : R) *
        topNodeReduction R m (topNodeDifference R m f hf (rightCoordinate (e))) +
      rightCoordinate (0 : R) *
        topNodeReduction R m (topNodeDifference R m f hf (leftCoordinate (e))) = 0 := by
  let x := leftCoordinate (e)
  let y := rightCoordinate (e)
  let a := topNodeDifference R m f hf x
  let b := topNodeDifference R m f hf y
  let t := algebraMap (S) (B) ((e) ^ (m + 1))
  have hx : f x = x + t * a := by
    have he : t * a = f x - x :=
      (Algebra.smul_def ((e) ^ (m + 1)) a).symm.trans
        (topNodeDifference_spec R m f hf x)
    exact (sub_eq_iff_eq_add.mp he.symm).trans (add_comm _ _)
  have hy : f y = y + t * b := by
    have he : t * b = f y - y :=
      (Algebra.smul_def ((e) ^ (m + 1)) b).symm.trans
        (topNodeDifference_spec R m f hf y)
    exact (sub_eq_iff_eq_add.mp he.symm).trans (add_comm _ _)
  have hp : (x + t * a) * (y + t * b) = algebraMap (S) (B) (e) := by
    rw [← hx, ← hy, ← map_mul, coordinate_relation, f.commutes]
  have he : (e) ^ (m + 1) • (x * b + y * a) = 0 := by
    apply (Algebra.smul_def ((e) ^ (m + 1)) (x * b + y * a)).trans
    have hxy : x * y = algebraMap (S) (B) (e) := coordinate_relation (e)
    have ht : t ^ 2 = 0 := by
      dsimp only [t]
      rw [map_pow]
      exact topNode_parameter_sq R m
    linear_combination hp - hxy - a * b * ht
  have hr := (topNode_parameter_annihilator R m _).mp he
  simpa only [x, y, a, b, (topNodeReduction R m).map_add, (topNodeReduction R m).map_mul,
    topNodeReduction_left, topNodeReduction_right] using hr

/-- The actual reduced coordinate errors define a derivation on the original split-node quotient. -/
def topNodeDifferenceDerivation : Derivation R (C₀) (C₀) :=
  derivationOfCoordinates (0 : R)
    (topNodeReduction R m (topNodeDifference R m f hf (leftCoordinate (e))))
    (topNodeReduction R m (topNodeDifference R m f hf (rightCoordinate (e))))
    (by simpa only [smul_eq_mul] using topNodeDifference_relation R m f hf)

/-- Transport the constructed vector field through the original node equalizer comparison. -/
def topNodeEqualizerDerivation :
    Derivation R (PolygonNodeEqualizer.A (R := R)) (PolygonNodeEqualizer.A (R := R)) where
  toLinearMap := (specialFiberEquiv R).toLinearEquiv.toLinearMap.comp
    ((topNodeDifferenceDerivation R m f hf).toLinearMap.comp
      (specialFiberEquiv R).symm.toLinearEquiv.toLinearMap)
  map_one_eq_zero' := by simp
  leibniz' a b := by
    change specialFiberEquiv R (topNodeDifferenceDerivation R m f hf
      ((specialFiberEquiv R).symm (a * b))) =
        a * specialFiberEquiv R (topNodeDifferenceDerivation R m f hf
          ((specialFiberEquiv R).symm b)) +
        b * specialFiberEquiv R (topNodeDifferenceDerivation R m f hf
          ((specialFiberEquiv R).symm a))
    rw [map_mul (specialFiberEquiv R).symm a b,
      (topNodeDifferenceDerivation R m f hf).leibniz]
    simp only [smul_eq_mul, map_add (specialFiberEquiv R), map_mul (specialFiberEquiv R),
      (specialFiberEquiv R).apply_symm_apply]

end FLT.Mazur.PolygonInfinitesimalStages

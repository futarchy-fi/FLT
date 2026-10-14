/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonScaledReciprocal
public import FLT.Mazur.LaurentUnitPoints
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Scaled Laurent coordinates on entire scheme points

Scaling and scaled inversion retain the coefficient map and act on units of
any test algebra. These equalities concern full morphisms of schemes, including
nonreduced test algebras, rather than only their underlying topological points.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentUnitPoints
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- Evaluation after scaling multiplies by the image of the original coefficient unit. -/
theorem evalUnit_scaling (a : Rˣ) (q : Bˣ) :
    (evalUnit (R := R) q).comp (PolygonScaledReciprocal.scaling a) =
      evalUnit (Units.map (algebraMap R B) a * q) := by
  apply pointsEquiv.injective
  change pointUnit _ = pointUnit _
  rw [pointUnit_evalUnit]
  apply Units.ext
  change evalUnit q (PolygonChartScaling.laurent a (LaurentPolynomial.T 1)) = _
  rw [PolygonChartScaling.laurent_T_one, map_mul, evalUnit_C, evalUnit_T, zpow_one]
  rfl

/-- Evaluation after scaled inversion retains the original coefficient unit. -/
theorem evalUnit_reciprocal (a : Rˣ) (q : Bˣ) :
    (evalUnit (R := R) q).comp (PolygonScaledReciprocal.reciprocal a) =
      evalUnit (Units.map (algebraMap R B) a / q) := by
  apply pointsEquiv.injective
  change pointUnit _ = pointUnit _
  rw [pointUnit_evalUnit]
  apply Units.ext
  change evalUnit q (PolygonScaledReciprocal.reciprocal a (LaurentPolynomial.T 1)) = _
  rw [PolygonScaledReciprocal.reciprocal_T, map_mul, evalUnit_C, evalUnit_T]
  simp only [zpow_neg, zpow_one]
  rfl

universe u
variable {S C : Type u} [CommRing S] [CommRing C] [Algebra S C]

/-- The scaling substitution acts on the entire affine Laurent point. -/
@[reassoc] theorem spec_evalUnit_scaling (a : Sˣ) (q : Cˣ) :
    Spec.map (CommRingCat.ofHom (evalUnit (R := S) q).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling a).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (evalUnit (R := S) (Units.map (algebraMap S C) a * q)).toRingHom) := by
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (evalUnit_scaling a q)

/-- The scaled reciprocal substitution acts on the entire affine Laurent point. -/
@[reassoc] theorem spec_evalUnit_reciprocal (a : Sˣ) (q : Cˣ) :
    Spec.map (CommRingCat.ofHom (evalUnit (R := S) q).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.reciprocal a).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (evalUnit (R := S) (Units.map (algebraMap S C) a / q)).toRingHom) := by
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (evalUnit_reciprocal a q)

end FLT.Mazur.LaurentUnitPoints

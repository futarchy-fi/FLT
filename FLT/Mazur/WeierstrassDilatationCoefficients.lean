/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationAlgebra

/-!
# Coefficient extension of the actual divided chart

The universal divided coordinates and their equation commute with coefficient
extension. These concrete maps will identify both the generic and special
fibers of the same integral chart.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassDilatation

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- Every algebra map sends the universal coordinates to an actual divided solution. -/
theorem equation_map {S : Type*} [CommRing S] [Algebra R S]
    (f : Coordinate W s b3 b4 b6 →ₐ[R] S) :
    f (y W s b3 b4 b6) ^ 2 +
        (algebraMap R S W.a₁ * f (x W s b3 b4 b6) + algebraMap R S b3) *
          f (y W s b3 b4 b6) =
      algebraMap R S s * f (x W s b3 b4 b6) ^ 3 +
        algebraMap R S W.a₂ * f (x W s b3 b4 b6) ^ 2 +
        algebraMap R S b4 * f (x W s b3 b4 b6) + algebraMap R S b6 := by
  simpa only [map_add, map_mul, map_pow, AlgHom.commutes] using
    congrArg f (equation W s b3 b4 b6)

variable (S : Type*) [CommRing S] [Algebra R S]

/-- The specialized actual coordinate algebra with its original coefficient map. -/
abbrev ExtendedCoordinate := Coordinate (W.map (algebraMap R S))
  (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)

/-- The specialized universal equation still holds as an equation over the original ring. -/
theorem coefficient_equation :
    let u := x (W.map (algebraMap R S))
      (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)
    let v := y (W.map (algebraMap R S))
      (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)
    v ^ 2 + (algebraMap R (ExtendedCoordinate W s b3 b4 b6 S) W.a₁ * u +
        algebraMap R _ b3) * v =
      algebraMap R _ s * u ^ 3 + algebraMap R _ W.a₂ * u ^ 2 +
        algebraMap R _ b4 * u + algebraMap R _ b6 := by
  simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    ← IsScalarTower.algebraMap_apply R S] using
    equation (W.map (algebraMap R S))
      (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)

/-- The actual coordinate map induced by extending coefficients. -/
def coefficientMap : Coordinate W s b3 b4 b6 →ₐ[R] ExtendedCoordinate W s b3 b4 b6 S :=
  evaluation W s b3 b4 b6
    (x (W.map (algebraMap R S))
      (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6))
    (y (W.map (algebraMap R S))
      (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6))
    (coefficient_equation W s b3 b4 b6 S)

/-- Coefficient extension preserves the first divided coordinate. -/
@[simp] theorem coefficientMap_x :
    coefficientMap W s b3 b4 b6 S (x W s b3 b4 b6) =
      x (W.map (algebraMap R S))
        (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) :=
  evaluation_x W s b3 b4 b6 _ _ _

/-- Coefficient extension preserves the second divided coordinate. -/
@[simp] theorem coefficientMap_y :
    coefficientMap W s b3 b4 b6 S (y W s b3 b4 b6) =
      y (W.map (algebraMap R S))
        (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) :=
  evaluation_y W s b3 b4 b6 _ _ _

end FLT.Mazur.WeierstrassDilatation

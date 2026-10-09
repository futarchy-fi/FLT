/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXAlgebra

/-!
# Coefficient extension of the actual horizontal chart

The universal incidence coordinates and their equation commute with coefficient
extension. These concrete maps will identify both the generic and special
fibers of the same integral chart.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassModificationX

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- Every algebra map sends the universal coordinates to an actual incidence solution. -/
theorem equation_map {S : Type*} [CommRing S] [Algebra R S]
    (f : Coordinate W s b3 b4 b6 →ₐ[R] S) :
    f (t W s b3 b4 b6) *
      (f (v W s b3 b4 b6) ^ 2 +
        (algebraMap R S W.a₁ + algebraMap R S b3 * f (t W s b3 b4 b6)) *
          f (v W s b3 b4 b6) -
        (algebraMap R S W.a₂ + algebraMap R S b4 * f (t W s b3 b4 b6) +
          algebraMap R S b6 * f (t W s b3 b4 b6) ^ 2)) = algebraMap R S s := by
  simpa only [x, map_sub, map_add, map_mul, map_pow, AlgHom.commutes] using
    congrArg f (incidence W s b3 b4 b6)

variable (S : Type*) [CommRing S] [Algebra R S]

/-- The specialized actual coordinate algebra with its original coefficient map. -/
abbrev ExtendedCoordinate := Coordinate (W.map (algebraMap R S))
  (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)

/-- The specialized universal equation still holds as an equation over the original ring. -/
theorem coefficient_equation :
    let u := t (W.map (algebraMap R S))
      (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)
    let v := v (W.map (algebraMap R S))
      (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)
    u * (v ^ 2 + (algebraMap R (ExtendedCoordinate W s b3 b4 b6 S) W.a₁ +
      algebraMap R _ b3 * u) * v -
        (algebraMap R _ W.a₂ + algebraMap R _ b4 * u + algebraMap R _ b6 * u ^ 2)) =
          algebraMap R _ s := by
  simpa only [x, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    ← IsScalarTower.algebraMap_apply R S] using
    incidence (W.map (algebraMap R S))
      (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)

/-- The actual coordinate map induced by extending coefficients. -/
def coefficientMap : Coordinate W s b3 b4 b6 →ₐ[R] ExtendedCoordinate W s b3 b4 b6 S :=
  evaluation W s b3 b4 b6
    (t (W.map (algebraMap R S))
      (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6))
    (v (W.map (algebraMap R S))
      (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6))
    (coefficient_equation W s b3 b4 b6 S)

/-- Coefficient extension preserves the first incidence coordinate. -/
@[simp] theorem coefficientMap_t :
    coefficientMap W s b3 b4 b6 S (t W s b3 b4 b6) =
      t (W.map (algebraMap R S))
        (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) :=
  evaluation_t W s b3 b4 b6 _ _ _

/-- Coefficient extension preserves the second incidence coordinate. -/
@[simp] theorem coefficientMap_v :
    coefficientMap W s b3 b4 b6 S (v W s b3 b4 b6) =
      v (W.map (algebraMap R S))
        (algebraMap R S s) (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) :=
  evaluation_v W s b3 b4 b6 _ _ _

end FLT.Mazur.WeierstrassModificationX

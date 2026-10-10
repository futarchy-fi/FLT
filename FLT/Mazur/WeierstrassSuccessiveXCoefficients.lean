/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXAlgebra

/-!
# Coefficient extension retains all three successive chart coordinates

The divided equation and incidence equation remain valid after any base
algebra map. This constructs the actual coefficient map without eliminating
the retained horizontal coordinate in a singular fiber.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- Every algebra map preserves the actual successive divided equation. -/
theorem equation_map {S : Type*} [CommRing S] [Algebra R S]
    (f : Coordinate W s π b3 b4 b6 →ₐ[R] S) :
    f (coord W s π b3 b4 b6 1) ^ 2 +
      (algebraMap R S W.a₁ + algebraMap R S b3 * f (coord W s π b3 b4 b6 0)) *
        f (coord W s π b3 b4 b6 1) =
      algebraMap R S s * f (coord W s π b3 b4 b6 2) + algebraMap R S W.a₂ +
        algebraMap R S b4 * f (coord W s π b3 b4 b6 0) +
        algebraMap R S b6 * f (coord W s π b3 b4 b6 0) ^ 2 := by
  simpa only [map_add, map_mul, map_pow, AlgHom.commutes] using
    congrArg f (equation W s π b3 b4 b6)

/-- Every algebra map also preserves the retained incidence equation. -/
theorem incidence_map {S : Type*} [CommRing S] [Algebra R S]
    (f : Coordinate W s π b3 b4 b6 →ₐ[R] S) :
    f (coord W s π b3 b4 b6 0) * f (coord W s π b3 b4 b6 2) = algebraMap R S π := by
  simpa only [map_mul, AlgHom.commutes] using congrArg f (incidence W s π b3 b4 b6)

variable (S : Type*) [CommRing S] [Algebra R S]

/-- The actual three-generator equation algebra after extending coefficients. -/
abbrev ExtendedCoordinate := Coordinate (W.map (algebraMap R S))
  (algebraMap R S s) (algebraMap R S π)
  (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)

/-- The three actual extended coordinates. -/
def extendedCoord (i : Fin 3) : ExtendedCoordinate W s π b3 b4 b6 S :=
  coord (W.map (algebraMap R S)) (algebraMap R S s) (algebraMap R S π)
    (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6) i

/-- The extended equation retains the original coefficient algebra structure. -/
theorem coefficient_equation :
    let c := extendedCoord W s π b3 b4 b6 S
    c 1 ^ 2 + (algebraMap R _ W.a₁ + algebraMap R _ b3 * c 0) * c 1 =
      algebraMap R _ s * c 2 + algebraMap R _ W.a₂ +
        algebraMap R _ b4 * c 0 + algebraMap R _ b6 * c 0 ^ 2 := by
  simpa only [extendedCoord, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    ← IsScalarTower.algebraMap_apply R S] using
    equation (W.map (algebraMap R S)) (algebraMap R S s) (algebraMap R S π)
      (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)

/-- The extended incidence equation retains the original parameter. -/
theorem coefficient_incidence :
    extendedCoord W s π b3 b4 b6 S 0 * extendedCoord W s π b3 b4 b6 S 2 =
      algebraMap R _ π := by
  simpa only [extendedCoord, ← IsScalarTower.algebraMap_apply R S] using
    incidence (W.map (algebraMap R S)) (algebraMap R S s) (algebraMap R S π)
      (algebraMap R S b3) (algebraMap R S b4) (algebraMap R S b6)

/-- The actual coefficient-extension map on the successive chart. -/
def coefficientMap : Coordinate W s π b3 b4 b6 →ₐ[R] ExtendedCoordinate W s π b3 b4 b6 S :=
  evaluation W s π b3 b4 b6 (extendedCoord W s π b3 b4 b6 S)
    (coefficient_equation W s π b3 b4 b6 S) (coefficient_incidence W s π b3 b4 b6 S)

/-- All three actual chart generators survive coefficient extension with their names. -/
@[simp] theorem coefficientMap_coord (i : Fin 3) :
    coefficientMap W s π b3 b4 b6 S (coord W s π b3 b4 b6 i) =
      extendedCoord W s π b3 b4 b6 S i := evaluation_coord _ _ _ _ _ _ _ _ _ i

end FLT.Mazur.WeierstrassSuccessiveX

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.QuadraticIncidenceInvolution
public import FLT.Mazur.WeierstrassModificationXPolynomialFactors

/-!
# Reflection of the full original initial chart

The polynomial coefficient algebra remains fixed. Reflection exchanges the
small and opposite factors with a minus sign and preserves the original x.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "A" => Coordinate W s b3 b4 b6

/-- The original full initial involution, before any localization. -/
def initialReflection : A ≃ₐ[R[X]] A :=
  QuadraticIncidenceTranslation.reflectionEquiv X (C s)
    (polynomialSlopeLinear W b3) (polynomialSlopeConstant W b4 b6)

/-- The involution preserves the original incidence parameter. -/
@[simp] theorem initialReflection_t :
    initialReflection W s b3 b4 b6 (t W s b3 b4 b6) = t W s b3 b4 b6 :=
  (initialReflection W s b3 b4 b6).commutes X

/-- Reflection sends the original slope to the opposite slope. -/
@[simp] theorem initialReflection_v :
    initialReflection W s b3 b4 b6 (v W s b3 b4 b6) =
      -v W s b3 b4 b6 - algebraMap R[X] A (polynomialSlopeLinear W b3) :=
  QuadraticIncidenceTranslation.reflection_root ..

/-- The original reflection is its own inverse on all functions. -/
theorem initialReflection_symm :
    (initialReflection W s b3 b4 b6).symm = initialReflection W s b3 b4 b6 := rfl

/-- The original horizontal coordinate is fixed, retaining every cubic coefficient. -/
theorem initialReflection_x :
    initialReflection W s b3 b4 b6 (x W s b3 b4 b6) = x W s b3 b4 b6 := by
  have hc (z : R) : initialReflection W s b3 b4 b6 (algebraMap R A z) =
      algebraMap R A z := ((initialReflection W s b3 b4 b6).restrictScalars R).commutes z
  simp only [x, map_sub, map_add, map_mul, map_pow, initialReflection_v, initialReflection_t,
    hc, polynomialSlopeLinear]
  have hd (z : R) : algebraMap R[X] A (C z) = algebraMap R A z :=
    (IsScalarTower.algebraMap_apply R R[X] A z).symm
  simp only [hd, t]
  ring

/-- Reflection exchanges the small tangent factor with the negative opposite factor. -/
theorem initialReflection_small (r : R[X]) :
    initialReflection W s b3 b4 b6 (polynomialSmallFactor W s b3 b4 b6 r) =
      -polynomialOppositeFactor W s b3 b4 b6 r := by
  simp only [polynomialSmallFactor, polynomialOppositeFactor, map_sub, initialReflection_v,
    AlgEquiv.commutes, map_add]
  ring

/-- Reflection exchanges the opposite factor with the negative small factor. -/
theorem initialReflection_opposite (r : R[X]) :
    initialReflection W s b3 b4 b6 (polynomialOppositeFactor W s b3 b4 b6 r) =
      -polynomialSmallFactor W s b3 b4 b6 r := by
  simp only [polynomialSmallFactor, polynomialOppositeFactor, map_add, initialReflection_v,
    AlgEquiv.commutes]
  ring

end FLT.Mazur.WeierstrassModificationX

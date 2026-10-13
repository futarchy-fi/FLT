/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberConic
public import FLT.Mazur.WeierstrassModificationXSlopeOpen
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The full shifted infinity boundary is its original punctured slope line

Inverting the conic factor times the root-shifted slope kills incidence.
The entire original localization is the slope line with the corresponding
three-factor product inverted; no shifted root is discarded.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c r : R)
local notation "F" => FiberCoordinate a c
local notation "q" => fiberConicFactor a c
local notation "z" => fiberV a c + algebraMap R F r
local notation "O" => Localization.Away (q * z)
local notation "p" => slopePolynomial a * (X + C r)
local notation "P" => Localization.Away p
local notation "t" => algebraMap F O (fiberT a c)
local notation "v" => algebraMap F O (fiberV a c)

/-- Inverting the shifted original vertical function makes the entire conic factor a unit. -/
theorem fiberShiftedInfinity_factor_unit : IsUnit (algebraMap F O q) :=
  isUnit_of_mul_isUnit_left (by
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit (q * z))

/-- Incidence vanishes throughout the full shifted infinity boundary. -/
theorem fiberShiftedInfinity_t : t = 0 := by
  apply (fiberShiftedInfinity_factor_unit a c r).mul_right_cancel
  rw [← map_mul, fiberConicFactor, fiber_relation, map_zero, zero_mul]

/-- The conic factor retains the product of both original tangent slopes. -/
theorem fiberShiftedInfinity_factor :
    algebraMap F O q = v * (v + algebraMap R O a) := by
  change algebraMap F O (fiberV a c * (fiberV a c + algebraMap R F a) -
    algebraMap R F c * fiberT a c ^ 2) = _
  rw [map_sub, map_mul, map_add, map_mul, map_pow,
    fiberShiftedInfinity_t, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero,
    ← IsScalarTower.algebraMap_apply]

/-- The full original incidence restriction extends to the shifted boundary. -/
def fiberShiftedInfinityToSlope : O →ₐ[R] P :=
  IsLocalization.Away.liftAlgHom
    (f := (IsScalarTower.toAlgHom R R[X] P).comp (fiberIncidenceMap a c)) (q * z) (by
      change IsUnit (algebraMap R[X] P (fiberIncidenceMap a c (q * z)))
      rw [map_mul, map_add, fiberIncidenceMap_factor, fiberIncidenceMap_v,
        AlgHom.commutes]
      exact IsLocalization.Away.algebraMap_isUnit p)

/-- The shifted boundary restriction preserves every function of the full fiber. -/
theorem fiberShiftedInfinityToSlope_base (w : F) :
    fiberShiftedInfinityToSlope a c r (algebraMap F O w) =
      algebraMap R[X] P (fiberIncidenceMap a c w) := by
  rw [fiberShiftedInfinityToSlope, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The inverse map evaluates the original slope without changing its shift. -/
def slopeToFiberShiftedInfinity : P →ₐ[R] O :=
  IsLocalization.Away.liftAlgHom (f := aeval v) p (by
    have h := IsLocalization.Away.algebraMap_isUnit (S := O) (q * z)
    simpa only [map_mul, map_add, fiberShiftedInfinity_factor,
      ← IsScalarTower.algebraMap_apply R F O, slopePolynomial, aeval_X, aeval_C] using h)

/-- The reverse comparison preserves every polynomial slope function. -/
theorem slopeToFiberShiftedInfinity_base (w : R[X]) :
    slopeToFiberShiftedInfinity a c r (algebraMap R[X] P w) = aeval v w := by
  rw [slopeToFiberShiftedInfinity, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The complete shifted fiber boundary and the full punctured slope algebra coincide. -/
def fiberShiftedInfinitySlopeEquiv : O ≃ₐ[R] P := by
  apply AlgEquiv.ofAlgHom (fiberShiftedInfinityToSlope a c r)
    (slopeToFiberShiftedInfinity a c r)
  · apply IsLocalization.algHom_ext (Submonoid.powers p)
    apply Polynomial.algHom_ext
    change fiberShiftedInfinityToSlope a c r
      (slopeToFiberShiftedInfinity a c r (algebraMap R[X] P X)) = algebraMap R[X] P X
    rw [slopeToFiberShiftedInfinity_base, aeval_X,
      fiberShiftedInfinityToSlope_base, fiberIncidenceMap_v]
  · apply IsLocalization.algHom_ext (Submonoid.powers (q * z))
    apply fiber_hom_ext a c
    · change slopeToFiberShiftedInfinity a c r
        (fiberShiftedInfinityToSlope a c r t) = t
      rw [fiberShiftedInfinityToSlope_base, fiberIncidenceMap_t,
        map_zero, map_zero, fiberShiftedInfinity_t]
    · change slopeToFiberShiftedInfinity a c r
        (fiberShiftedInfinityToSlope a c r v) = v
      rw [fiberShiftedInfinityToSlope_base, fiberIncidenceMap_v,
        slopeToFiberShiftedInfinity_base, aeval_X]

/-- Every original function is preserved by the entire shifted localization comparison. -/
theorem fiberShiftedInfinitySlopeEquiv_base (w : F) :
    fiberShiftedInfinitySlopeEquiv a c r (algebraMap F O w) =
      algebraMap R[X] P (fiberIncidenceMap a c w) :=
  fiberShiftedInfinityToSlope_base a c r w

end FLT.Mazur.WeierstrassModificationX

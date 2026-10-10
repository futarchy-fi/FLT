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
# The full horizontal exterior is the original punctured slope line

Inverting the conic factor kills the incidence coordinate. The entire
localization is the slope line with both ordered tangent roots removed,
even over nonreduced coefficient rings and with arbitrary divided constant.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (a c : R)
local notation "F" => FiberCoordinate a c
local notation "q" => fiberConicFactor a c
local notation "O" => Localization.Away q
local notation "P" => SlopeOpen a
local notation "t" => algebraMap F O (fiberT a c)
local notation "v" => algebraMap F O (fiberV a c)

/-- The incidence coordinate vanishes on the entire horizontal exterior. -/
theorem fiberExterior_t : t = 0 := by
  apply (IsLocalization.Away.algebraMap_isUnit q).mul_right_cancel
  rw [← map_mul, fiberConicFactor, fiber_relation, map_zero, zero_mul]

/-- The original conic factor restricts to the ordered tangent product. -/
theorem fiberExterior_factor : algebraMap F O q = v * (v + algebraMap R O a) := by
  change algebraMap F O (fiberV a c * (fiberV a c + algebraMap R F a) -
    algebraMap R F c * fiberT a c ^ 2) = _
  rw [map_sub, map_mul, map_add, map_mul, map_pow,
    fiberExterior_t, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero,
    ← IsScalarTower.algebraMap_apply]

/-- Both original tangent factors are units throughout the horizontal exterior. -/
theorem fiberExterior_units : IsUnit v ∧ IsUnit (v + algebraMap R O a) := by
  have h : IsUnit (algebraMap F O q) := IsLocalization.Away.algebraMap_isUnit q
  rw [fiberExterior_factor] at h
  exact ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩

/-- The first infinity and horizontal boundaries are the same entire open set. -/
theorem fiberExterior_infinity_open :
    PrimeSpectrum.basicOpen (q * fiberV a c) = PrimeSpectrum.basicOpen q := by
  rw [PrimeSpectrum.basicOpen_mul, inf_eq_left]
  exact (PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit (S := O)).mpr
    (fiberExterior_units a c).1

/-- The original incidence restriction extends to the complete horizontal localization. -/
def fiberExteriorToSlope : O →ₐ[R] P :=
  IsLocalization.Away.liftAlgHom
    (f := (Algebra.algHom R R[X] P).comp (fiberIncidenceMap a c)) q (by
      change IsUnit (algebraMap R[X] P (fiberIncidenceMap a c q))
      rw [fiberIncidenceMap_factor]
      exact IsLocalization.Away.algebraMap_isUnit (slopePolynomial a))

/-- Every original fiber function restricts through the original incidence map. -/
theorem fiberExteriorToSlope_base (z : F) :
    fiberExteriorToSlope a c (algebraMap F O z) =
      algebraMap R[X] P (fiberIncidenceMap a c z) := by
  rw [fiberExteriorToSlope, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The reverse map retains the original slope function. -/
def slopeToFiberExterior : P →ₐ[R] O :=
  IsLocalization.Away.liftAlgHom (f := aeval v) (slopePolynomial a) (by
    simpa only [slopePolynomial, map_mul, map_add, aeval_X, aeval_C] using
      (fiberExterior_units a c).1.mul (fiberExterior_units a c).2)

/-- Polynomial slope functions have their original evaluation in the full exterior. -/
theorem slopeToFiberExterior_base (p : R[X]) :
    slopeToFiberExterior a c (algebraMap R[X] P p) = aeval v p := by
  rw [slopeToFiberExterior, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The original slope coordinate is unchanged by the reverse comparison. -/
theorem slopeToFiberExterior_z : slopeToFiberExterior a c (slopeZ a) = v := by
  rw [slopeZ, slopeToFiberExterior_base, aeval_X]

/-- The comparison is the identity on all functions of the full exterior. -/
theorem slopeToFiberExterior_comp :
    (slopeToFiberExterior a c).comp (fiberExteriorToSlope a c) = AlgHom.id R O := by
  apply IsLocalization.algHom_ext (Submonoid.powers q)
  apply fiber_hom_ext a c
  · change slopeToFiberExterior a c (fiberExteriorToSlope a c t) = t
    rw [fiberExteriorToSlope_base, fiberIncidenceMap_t, map_zero, map_zero, fiberExterior_t]
  · change slopeToFiberExterior a c (fiberExteriorToSlope a c v) = v
    rw [fiberExteriorToSlope_base, fiberIncidenceMap_v, slopeToFiberExterior_base, aeval_X]

/-- The comparison is the identity on all functions of the punctured slope line. -/
theorem fiberExteriorToSlope_comp :
    (fiberExteriorToSlope a c).comp (slopeToFiberExterior a c) = AlgHom.id R P := by
  apply IsLocalization.algHom_ext (Submonoid.powers (slopePolynomial a))
  apply Polynomial.algHom_ext
  change fiberExteriorToSlope a c (slopeToFiberExterior a c (slopeZ a)) = slopeZ a
  rw [slopeToFiberExterior_z, fiberExteriorToSlope_base, fiberIncidenceMap_v]
  rfl

/-- The whole horizontal exterior, with the original two tangent roots removed. -/
def fiberExteriorSlopeEquiv : O ≃ₐ[R] P :=
  AlgEquiv.ofAlgHom (fiberExteriorToSlope a c) (slopeToFiberExterior a c)
    (fiberExteriorToSlope_comp a c) (slopeToFiberExterior_comp a c)

/-- The full equivalence retains every original function restriction. -/
theorem fiberExteriorSlopeEquiv_base (z : F) :
    fiberExteriorSlopeEquiv a c (algebraMap F O z) =
      algebraMap R[X] P (fiberIncidenceMap a c z) := fiberExteriorToSlope_base a c z

end FLT.Mazur.WeierstrassModificationX

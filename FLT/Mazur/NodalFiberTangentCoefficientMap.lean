/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodalFiberTangentFraction
public import FLT.Mazur.NodalFiberCoefficientRingMap

/-!
# Coefficient restriction on entire fractional tangent neighborhoods

The localization map preserves both original node coordinates and their
fractional ratio. Independently named target parameters allow arithmetic
quotient restriction without replacing the full neighborhoods by punctures.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NodalFiber
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (s d : R) (s' d' : S) (hs : f s = s') (hd : f d = d')
local notation "N" => Coordinate s
local notation "N'" => Coordinate s'
local notation "L" => TangentOpen s d
local notation "L'" => TangentOpen s' d'
local notation "G" => coefficientRingMap f s s' hs

include hd in
/-- The node coefficient map preserves the entire deleted tangent divisor. -/
theorem tangentCoefficient_denominator :
    G (q s + algebraMap R N d) = q s' + algebraMap S N' d' := by
  rw [map_add, coefficientRingMap_q, coefficientRingMap_algebraMap, hd]

/-- Restriction of the original coefficients on every localized node function. -/
def tangentCoefficientRingMap : L →+* L' :=
  IsLocalization.Away.lift (q s + algebraMap R N d)
    (g := (algebraMap N' L').comp G) (by
      rw [RingHom.comp_apply, tangentCoefficient_denominator f s d s' d' hs hd]
      exact IsLocalization.Away.algebraMap_isUnit _)

/-- Coefficient restriction on unlocalized functions uses the original node map. -/
theorem tangentCoefficientRingMap_base (z : N) :
    tangentCoefficientRingMap f s d s' d' hs hd (algebraMap N L z) =
      algebraMap N' L' (G z) := IsLocalization.Away.lift_eq _ _ _

/-- Every scalar retains the specified arithmetic coefficient map. -/
theorem tangentCoefficientRingMap_scalar (z : R) :
    tangentCoefficientRingMap f s d s' d' hs hd (algebraMap R L z) =
      algebraMap S L' (f z) := by
  rw [IsScalarTower.algebraMap_apply R N L, tangentCoefficientRingMap_base,
    coefficientRingMap_algebraMap, ← IsScalarTower.algebraMap_apply S N' L']

/-- The full first coordinate survives coefficient restriction. -/
@[simp] theorem tangentCoefficientRingMap_p :
    tangentCoefficientRingMap f s d s' d' hs hd (tangentP s d) = tangentP s' d' := by
  rw [tangentP, tangentCoefficientRingMap_base, coefficientRingMap_p]
  rfl

/-- The full second coordinate survives coefficient restriction. -/
@[simp] theorem tangentCoefficientRingMap_q :
    tangentCoefficientRingMap f s d s' d' hs hd (tangentQ s d) = tangentQ s' d' := by
  rw [tangentQ, tangentCoefficientRingMap_base, coefficientRingMap_q]
  rfl

/-- The actual fractional coordinate follows the original coefficient restriction. -/
@[simp] theorem tangentCoefficientRingMap_fraction :
    tangentCoefficientRingMap f s d s' d' hs hd (tangentFraction s d) =
      tangentFraction s' d' := by
  have h := congrArg (tangentCoefficientRingMap f s d s' d' hs hd)
    (tangentFraction_denominator s d)
  rw [map_mul, map_add, tangentCoefficientRingMap_q,
    tangentCoefficientRingMap_scalar, hd] at h
  apply (tangent_denominator_isUnit s' d').mul_right_cancel
  rw [h, tangentFraction_denominator]

/-- Constants and both full node coordinates determine a map on the entire tangent open. -/
theorem tangent_ringHom_ext {T : Type*} [CommRing T] (g h : L →+* T)
    (hc : ∀ z, g (algebraMap R L z) = h (algebraMap R L z))
    (hp : g (tangentP s d) = h (tangentP s d))
    (hq : g (tangentQ s d) = h (tangentQ s d)) : g = h := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (q s + algebraMap R N d))
  apply coefficient_ringHom_ext
  · intro z
    simpa only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R N L] using hc z
  · exact hp
  · exact hq

end FLT.Mazur.NodalFiber

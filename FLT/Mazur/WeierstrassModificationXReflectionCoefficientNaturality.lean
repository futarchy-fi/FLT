/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXCoefficientRingMap
public import FLT.Mazur.WeierstrassModificationXInvolution

/-!
# Reflection retains every coefficient of the original initial equation

The full reflection commutes with arbitrary coefficient maps, including its
linear slope correction. This supplies the opposite-label coefficient square.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
local notation "U" => W.map f
local notation "A" => Coordinate W s b3 b4 b6
local notation "B" => Coordinate U (f s) (f b3) (f b4) (f b6)
local notation "c" => coefficientRingMap f W s b3 b4 b6
local notation "e" => initialReflection W s b3 b4 b6
local notation "e'" => initialReflection U (f s) (f b3) (f b4) (f b6)

/-- The complete polynomial-linear correction retains the original coefficient action. -/
theorem coefficientRingMap_slopeLinear :
    c (algebraMap R[X] A (polynomialSlopeLinear W b3)) =
      algebraMap S[X] B (polynomialSlopeLinear U (f b3)) := by
  have hR (a : R) : algebraMap R[X] A (C a) = algebraMap R A a :=
    (IsScalarTower.algebraMap_apply R R[X] A a).symm
  have hS (a : S) : algebraMap S[X] B (C a) = algebraMap S B a :=
    (IsScalarTower.algebraMap_apply S S[X] B a).symm
  simp only [polynomialSlopeLinear, map_add, map_mul, hR, hS]
  change c (algebraMap R A W.a₁) + c (algebraMap R A b3) * c (t W s b3 b4 b6) = _
  rw [coefficientRingMap_scalar, coefficientRingMap_scalar, coefficientRingMap_t]
  rfl

/-- The original reflection commutes on every full initial function. -/
theorem initialReflection_coefficient :
    (c).comp (e).toRingEquiv.toRingHom = (e').toRingEquiv.toRingHom.comp c := by
  apply coefficient_ringHom_ext W s b3 b4 b6
  · intro a
    change c (e (algebraMap R A a)) = e' (c (algebraMap R A a))
    rw [show e (algebraMap R A a) = algebraMap R A a from
      ((e).restrictScalars R).commutes a, coefficientRingMap_scalar]
    exact (((e').restrictScalars S).commutes (f a)).symm
  · change c (e (t W s b3 b4 b6)) = e' (c (t W s b3 b4 b6))
    rw [initialReflection_t, coefficientRingMap_t, initialReflection_t]
  · change c (e (v W s b3 b4 b6)) = e' (c (v W s b3 b4 b6))
    rw [initialReflection_v, coefficientRingMap_v, initialReflection_v,
      map_sub, map_neg, coefficientRingMap_v, coefficientRingMap_slopeLinear]

end FLT.Mazur.WeierstrassModificationX

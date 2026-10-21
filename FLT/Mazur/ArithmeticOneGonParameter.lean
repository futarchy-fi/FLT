/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingEquation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# An algebraic parameter for the arithmetic one-gon

The ring Z[t,1/(1+432t)] represents parameters with invertible complementary
discriminant factor. No characteristic, completion, or invertibility of t is imposed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ArithmeticOneGonParameter
open Polynomial

/-- The factor removed from the integral parameter line. -/
def denominator : Polynomial ℤ := 1 + 432 * X

/-- The algebraic parameter ring, retaining the singular parameter zero. -/
abbrev ParameterRing := Localization.Away denominator

/-- The universal degeneration parameter. -/
def parameter : ParameterRing := algebraMap (Polynomial ℤ) ParameterRing X

/-- The complementary discriminant factor is invertible on this parameter space. -/
theorem factor_isUnit : IsUnit (1 + 432 * parameter) := by
  simpa only [denominator, map_add, map_one, map_mul, map_ofNat, parameter] using
    (IsLocalization.Away.algebraMap_isUnit denominator :
      IsUnit (algebraMap (Polynomial ℤ) ParameterRing denominator))

variable {R A : Type} [CommRing R] [CommRing A]

/-- Evaluation of the removed polynomial is its original arithmetic expression. -/
theorem eval_denominator (t : R) :
    Polynomial.eval₂RingHom (Int.castRingHom R) t denominator = 1 + 432 * t := by
  simp [denominator]

/-- Every permitted arithmetic parameter defines an actual coefficient homomorphism. -/
def specialize (t : R) (ht : IsUnit (1 + 432 * t)) : ParameterRing →+* R :=
  IsLocalization.Away.lift denominator ((eval_denominator t).symm ▸ ht)

/-- Specialization agrees with polynomial evaluation before localization. -/
@[simp] theorem specialize_algebraMap (t : R) (ht : IsUnit (1 + 432 * t))
    (p : Polynomial ℤ) :
    specialize t ht (algebraMap (Polynomial ℤ) ParameterRing p) =
      Polynomial.eval₂RingHom (Int.castRingHom R) t p :=
  IsLocalization.Away.lift_eq _ _ _

/-- The universal parameter specializes to the prescribed parameter. -/
@[simp] theorem specialize_parameter (t : R) (ht : IsUnit (1 + 432 * t)) :
    specialize t ht parameter = t := by
  simp [parameter]

/-- A homomorphism from the parameter ring is determined by its degeneration parameter. -/
@[ext] theorem hom_ext (f g : ParameterRing →+* R) (h : f parameter = g parameter) :
    f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers denominator)
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · exact h

/-- Specialization is natural for arbitrary coefficient maps, including residue maps. -/
theorem specialize_natural (t : R) (ht : IsUnit (1 + 432 * t)) (f : R →+* A)
    (hf : IsUnit (1 + 432 * f t)) :
    f.comp (specialize t ht) = specialize (f t) hf := by
  apply hom_ext
  simp

/-- Every homomorphism satisfies the original arithmetic open condition. -/
theorem hom_factor_isUnit (f : ParameterRing →+* R) : IsUnit (1 + 432 * f parameter) := by
  simpa only [map_add, map_one, map_mul, map_ofNat] using factor_isUnit.map f

/-- The representing equivalence retains the original parameter, not only its closed fiber. -/
def homEquiv : (ParameterRing →+* R) ≃ {t : R // IsUnit (1 + 432 * t)} where
  toFun f := ⟨f parameter, hom_factor_isUnit f⟩
  invFun t := specialize t.val t.property
  left_inv f := hom_ext _ f (specialize_parameter (f parameter) _)
  right_inv t := Subtype.ext (specialize_parameter t.val t.property)

/-- The full varying cubic equation specializes without any discriminant inversion. -/
theorem equation_specialize (t : R) (ht : IsUnit (1 + 432 * t)) :
    (OneGonSmoothing.equation parameter).map (specialize t ht) =
      OneGonSmoothing.equation t := by
  rw [OneGonSmoothing.equation_map, specialize_parameter]

end FLT.Mazur.ArithmeticOneGonParameter

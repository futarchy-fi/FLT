/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentQuadraticDifferenceFactors

/-!
# Inverting the corrected quadratic tangent factors

Finite nilpotent inversion recovers the difference and hence both original
coordinates. The construction works on the complete affine plane.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.NilpotentQuadraticDifference
variable {R : Type*} [CommRing R] (K : R[X])
  (I : Ideal R) (hI : IsNilpotent I) (hK : K ∈ I.map C)

/-- The nilpotent correction in the factor-difference equation. -/
def inverseCorrection : R[X] := X * (-factorRoot K I hI hK - factorRoot K I hI hK)

/-- The inverse correction has coefficients in the original arithmetic ideal. -/
theorem inverseCorrection_mem : inverseCorrection K I hI hK ∈ I.map C :=
  (I.map C).mul_mem_left _ ((I.map C).sub_mem
    ((I.map C).neg_mem (factorRoot_mem K I hI hK)) (factorRoot_mem K I hI hK))

variable {S : Type*} [CommRing S] (f : R →+* S) (p q : S)

/-- The original difference constructed from the corrected factor difference. -/
def inverseDifference : S :=
  NilpotentPolynomialInverse.extendedInverse I hI f (inverseCorrection K I hI hK)
    (inverseCorrection_mem K I hI hK) 1 isUnit_one (q - p)

local notation "D" => inverseDifference K I hI hK f p q
local notation "r" => factorRoot K I hI hK

/-- The recovered difference solves the exact factor-difference equation. -/
theorem inverseDifference_equation :
    D * (1 - Polynomial.eval₂ f D r - Polynomial.eval₂ f D r) = q - p := by
  have he := NilpotentPolynomialInverse.extendedInverse_equation I hI f
    (inverseCorrection K I hI hK) (inverseCorrection_mem K I hI hK) 1 isUnit_one (q - p)
  change 1 * D + (inverseCorrection K I hI hK).eval₂ f D = q - p at he
  simp only [inverseCorrection, eval₂_mul, eval₂_sub, eval₂_neg, eval₂_X] at he
  linear_combination he

/-- The full difference equation has only one solution. -/
theorem inverseDifference_unique {z w : S}
    (hz : z * (1 - (factorRoot K I hI hK).eval₂ f z -
      (factorRoot K I hI hK).eval₂ f z) = q - p)
    (hw : w * (1 - (factorRoot K I hI hK).eval₂ f w -
      (factorRoot K I hI hK).eval₂ f w) = q - p) : z = w := by
  apply NilpotentPolynomialInverse.extended_solution_unique I hI f
    (inverseCorrection K I hI hK) (inverseCorrection_mem K I hI hK) 1 isUnit_one (q - p)
  · simp only [inverseCorrection, eval₂_mul, eval₂_sub, eval₂_neg, eval₂_X]
    linear_combination hz
  · simp only [inverseCorrection, eval₂_mul, eval₂_sub, eval₂_neg, eval₂_X]
    linear_combination hw

/-- The recovered pair has exactly the recovered difference. -/
theorem inverseDifference_pair :
    (q + D * Polynomial.eval₂ f D r) - (p - D * Polynomial.eval₂ f D r) = D := by
  linear_combination -inverseDifference_equation K I hI hK f p q

/-- The first recovered coordinate maps to the prescribed first factor. -/
theorem inverseDifference_small :
    smallFactor K I hI hK f (p - D * Polynomial.eval₂ f D r)
      (q + D * Polynomial.eval₂ f D r) = p := by
  rw [smallFactor, inverseDifference_pair]
  ring

/-- The second recovered coordinate maps to the prescribed second factor. -/
theorem inverseDifference_opposite :
    oppositeFactor K I hI hK f (p - D * Polynomial.eval₂ f D r)
      (q + D * Polynomial.eval₂ f D r) = q := by
  rw [oppositeFactor, inverseDifference_pair]
  ring

/-- Evaluating the inverse on the original factors recovers the entire original difference. -/
theorem inverseDifference_original (u v : S) :
    inverseDifference K I hI hK f (smallFactor K I hI hK f u v)
      (oppositeFactor K I hI hK f u v) = v - u := by
  apply inverseDifference_unique K I hI hK f
    (smallFactor K I hI hK f u v) (oppositeFactor K I hI hK f u v)
  · exact inverseDifference_equation ..
  · exact (factors_difference K I hI hK f u v).symm

/-- The constructed inverse commutes with coefficient-preserving algebra maps. -/
theorem inverseDifference_map [Algebra R S] {T : Type*} [CommRing T] [Algebra R T]
    (g : S →ₐ[R] T) :
    g (inverseDifference K I hI hK (algebraMap R S) p q) =
      inverseDifference K I hI hK (algebraMap R T) (g p) (g q) := by
  apply inverseDifference_unique K I hI hK (algebraMap R T) (g p) (g q)
  · have he := congrArg g (inverseDifference_equation K I hI hK (algebraMap R S) p q)
    simpa only [map_mul, map_sub, map_one, Polynomial.algHom_eval₂_algebraMap] using he
  · exact inverseDifference_equation ..

end FLT.Mazur.NilpotentQuadraticDifference

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentPolynomialEvaluation

/-!
# Polynomial factors for a nilpotent quadratic difference correction

The small root of r²-r=K factors uv-(v-u)²K(v-u) without dividing by 2.
The factor difference is a unit-linear polynomial with nilpotent correction.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.NilpotentQuadraticDifference
variable {R : Type*} [CommRing R] (K : R[X])
  (I : Ideal R) (hI : IsNilpotent I) (hK : K ∈ I.map C)

/-- The polynomial small root used to absorb the entire quadratic correction. -/
def factorRoot : R[X] :=
  NilpotentQuadraticRoot.root (I.map C) (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI C)
    (-1) K (isUnit_one.neg) hK

/-- The polynomial factor root retains the nilpotent coefficient ideal. -/
theorem factorRoot_mem : factorRoot K I hI hK ∈ I.map C := NilpotentQuadraticRoot.root_mem ..

/-- The exact factor equation, requiring no inverse of 2. -/
theorem factorRoot_equation : factorRoot K I hI hK ^ 2 - factorRoot K I hI hK = K := by
  simpa only [factorRoot, neg_one_mul, sub_eq_add_neg] using
    NilpotentQuadraticRoot.root_equation (I.map C)
      (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI C) (-1) K (isUnit_one.neg) hK

variable {S : Type*} [CommRing S] (f : R →+* S) (u v : S)

/-- The first corrected factor of the translated terminal equation. -/
def smallFactor : S := u + (v - u) * (factorRoot K I hI hK).eval₂ f (v - u)

/-- The second corrected factor of the translated terminal equation. -/
def oppositeFactor : S := v - (v - u) * (factorRoot K I hI hK).eval₂ f (v - u)

/-- The factor product is exactly the original corrected product. -/
theorem factors_product : smallFactor K I hI hK f u v * oppositeFactor K I hI hK f u v =
    u * v - (v - u) ^ 2 * K.eval₂ f (v - u) := by
  have he := congrArg (Polynomial.eval₂ f (v - u)) (factorRoot_equation K I hI hK)
  simp only [eval₂_sub, eval₂_pow] at he
  simp only [smallFactor, oppositeFactor]
  linear_combination -(v - u) ^ 2 * he

/-- The factor difference is a unit-linear polynomial in the original difference. -/
theorem factors_difference : oppositeFactor K I hI hK f u v - smallFactor K I hI hK f u v =
    (v - u) * (1 - (factorRoot K I hI hK).eval₂ f (v - u) -
      (factorRoot K I hI hK).eval₂ f (v - u)) := by
  simp only [smallFactor, oppositeFactor]
  ring

/-- The first factor commutes with every coefficient-preserving algebra map. -/
theorem smallFactor_map [Algebra R S] {T : Type*} [CommRing T] [Algebra R T]
    (g : S →ₐ[R] T) :
    g (smallFactor K I hI hK (algebraMap R S) u v) =
      smallFactor K I hI hK (algebraMap R T) (g u) (g v) := by
  simp only [smallFactor, map_add, map_mul, map_sub, Polynomial.algHom_eval₂_algebraMap]

/-- The opposite factor commutes with every coefficient-preserving algebra map. -/
theorem oppositeFactor_map [Algebra R S] {T : Type*} [CommRing T] [Algebra R T]
    (g : S →ₐ[R] T) :
    g (oppositeFactor K I hI hK (algebraMap R S) u v) =
      oppositeFactor K I hI hK (algebraMap R T) (g u) (g v) := by
  simp only [oppositeFactor, map_sub, map_mul, Polynomial.algHom_eval₂_algebraMap]

end FLT.Mazur.NilpotentQuadraticDifference

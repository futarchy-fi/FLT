/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentQuadraticDifferenceFactors

/-!
# Arithmetic reduction of the corrected node factors

The finite quadratic correction preserves each factor modulo the original
nilpotent ideal, so invertibility of either translated factor is preserved.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.NilpotentQuadraticDifference
variable {R : Type*} [CommRing R] (K : R[X])
  (I : Ideal R) (hI : IsNilpotent I) (hK : K ∈ I.map C)
  {S : Type*} [CommRing S] (f : R →+* S) (u v : S)

/-- The first correction changes its factor only in the extended arithmetic ideal. -/
theorem smallFactor_sub_mem : smallFactor K I hI hK f u v - u ∈ I.map f := by
  have hm := (I.map f).mul_mem_left (v - u)
    (NilpotentPolynomialInverse.eval₂_mem I f (factorRoot K I hI hK)
      (factorRoot_mem K I hI hK) (v - u))
  simpa only [smallFactor, add_sub_cancel_left] using hm

/-- The opposite correction also keeps its original arithmetic reduction. -/
theorem oppositeFactor_sub_mem : oppositeFactor K I hI hK f u v - v ∈ I.map f := by
  have hm := (I.map f).neg_mem ((I.map f).mul_mem_left (v - u)
    (NilpotentPolynomialInverse.eval₂_mem I f (factorRoot K I hI hK)
      (factorRoot_mem K I hI hK) (v - u)))
  convert hm using 1
  simp only [oppositeFactor]
  ring

include hI in
/-- A unit remains a unit after a correction in the extended nilpotent ideal. -/
theorem isUnit_of_sub_mem {a b : S} (hb : IsUnit b) (h : a - b ∈ I.map f) : IsUnit a := by
  have hn := NilpotentQuadraticRoot.element_nilpotent (I.map f)
    (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI f) h
  have hu := hn.isUnit_add_left_of_commute hb (mul_comm (a - b) b)
  convert hu using 1
  ring

/-- The corrected first factor is invertible whenever the translated first factor is. -/
theorem smallFactor_isUnit (hu : IsUnit u) : IsUnit (smallFactor K I hI hK f u v) :=
  isUnit_of_sub_mem I hI f hu (smallFactor_sub_mem K I hI hK f u v)

/-- The corrected opposite factor is invertible whenever its translated factor is. -/
theorem oppositeFactor_isUnit (hv : IsUnit v) : IsUnit (oppositeFactor K I hI hK f u v) :=
  isUnit_of_sub_mem I hI f hv (oppositeFactor_sub_mem K I hI hK f u v)

end FLT.Mazur.NilpotentQuadraticDifference

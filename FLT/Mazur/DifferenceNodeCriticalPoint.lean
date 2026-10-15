/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DifferenceNodeAlgebra
public import FLT.Mazur.NilpotentPolynomialTaylor

/-!
# The constructed critical point and retained smoothing constant

The difference equation d + 2h'(d) = -b has a unique solution by finite
nilpotent inversion. The resulting constant is h(d) + h'(d)^2.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.DifferenceNode
variable {R : Type*} [CommRing R] (h : R[X]) (b : R)
  (I : Ideal R) (hI : IsNilpotent I) (hh : h ∈ I.map C)

/-- The critical tangent difference is constructed over the original coefficient ring. -/
def criticalDifference : R :=
  NilpotentPolynomialInverse.inverse I (h.derivative + h.derivative)
    ((I.map C).add_mem (NilpotentPolynomialInverse.derivative_mem I h hh)
      (NilpotentPolynomialInverse.derivative_mem I h hh)) hI 1 isUnit_one (-b)

/-- The small tangent coordinate of the critical point. -/
def criticalSlope : R := h.derivative.eval (criticalDifference h b I hI hh)

/-- The constructed critical point solves both gradient equations. -/
theorem criticalDifference_equation :
    criticalDifference h b I hI hh + criticalSlope h b I hI hh +
      criticalSlope h b I hI hh = -b := by
  have he := NilpotentPolynomialInverse.inverse_equation I (h.derivative + h.derivative)
    ((I.map C).add_mem (NilpotentPolynomialInverse.derivative_mem I h hh)
      (NilpotentPolynomialInverse.derivative_mem I h hh)) hI 1 isUnit_one (-b)
  simpa only [criticalDifference, criticalSlope, one_mul, eval_add, ← add_assoc] using he

/-- The constant-product smoothing parameter after translating the critical point. -/
def smoothingConstant : R :=
  h.eval (criticalDifference h b I hI hh) + criticalSlope h b I hI hh ^ 2

/-- The critical tangent shift lies in the original arithmetic ideal. -/
theorem criticalSlope_mem : criticalSlope h b I hI hh ∈ I := by
  simpa only [criticalSlope, eval₂_id, Ideal.map_id] using
    NilpotentPolynomialInverse.eval₂_mem I (RingHom.id R) h.derivative
      (NilpotentPolynomialInverse.derivative_mem I h hh) (criticalDifference h b I hI hh)

/-- The actual smoothing constant retains its arithmetic vanishing ideal. -/
theorem smoothingConstant_mem : smoothingConstant h b I hI hh ∈ I := by
  apply I.add_mem
  · simpa only [eval₂_id, Ideal.map_id] using
      NilpotentPolynomialInverse.eval₂_mem I (RingHom.id R) h hh
        (criticalDifference h b I hI hh)
  · exact I.pow_mem_of_mem (criticalSlope_mem h b I hI hh) 2 (by decide)

include hI hh in
/-- The tangent difference of the critical point is uniquely determined. -/
theorem criticalDifference_unique {z : R}
    (hz : z + h.derivative.eval z + h.derivative.eval z = -b) :
    z = criticalDifference h b I hI hh := by
  apply NilpotentPolynomialInverse.solution_unique I (h.derivative + h.derivative)
    ((I.map C).add_mem (NilpotentPolynomialInverse.derivative_mem I h hh)
      (NilpotentPolynomialInverse.derivative_mem I h hh)) hI 1 isUnit_one (-b)
  · simpa only [one_mul, eval_add, ← add_assoc] using hz
  · simpa only [one_mul, eval_add, ← add_assoc, criticalSlope] using
      criticalDifference_equation h b I hI hh

end FLT.Mazur.DifferenceNode

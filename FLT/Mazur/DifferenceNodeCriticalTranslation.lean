/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DifferenceNodeCriticalPoint

/-!
# Translating the full corrected product to its critical point

The translation removes exactly the linear Taylor term. The quadratic
remainder and the nonzero smoothing constant are both retained.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.DifferenceNode
variable {R : Type*} [CommRing R] (h : R[X]) (b : R)
  (I : Ideal R) (hI : IsNilpotent I) (hh : h ∈ I.map C)
  {S : Type*} [CommRing S] (f : R →+* S) (p q : S)
local notation "a" => criticalSlope h b I hI hh
local notation "z" => criticalDifference h b I hI hh
local notation "K" => NilpotentPolynomialInverse.quadraticRemainder h z

/-- The original tangent difference is the translated difference plus the critical value. -/
theorem criticalTranslation_difference :
    q - p - f b = (q + f a - (p - f a)) + f z := by
  have he := congrArg f (criticalDifference_equation h b I hI hh)
  simp only [map_add, map_neg] at he
  linear_combination -he

/-- Translation gives an exact identity between the original and centered equations. -/
theorem criticalTranslation_identity :
    p * q - h.eval₂ f (q - p - f b) =
      (p - f a) * (q + f a) - f (smoothingConstant h b I hI hh) -
        (q + f a - (p - f a)) ^ 2 *
          Polynomial.eval₂ f (q + f a - (p - f a)) K := by
  rw [criticalTranslation_difference h b I hI hh f p q,
    NilpotentPolynomialInverse.quadraticRemainder_eval]
  simp only [smoothingConstant, map_add, map_pow, criticalSlope]
  ring

/-- Every original point gives a centered point with the retained quadratic correction. -/
theorem criticalTranslation_relation
    (hpq : p * q = h.eval₂ f (q - p - f b)) :
    (p - f a) * (q + f a) = f (smoothingConstant h b I hI hh) +
      (q + f a - (p - f a)) ^ 2 *
        Polynomial.eval₂ f (q + f a - (p - f a)) K := by
  have he := criticalTranslation_identity h b I hI hh f p q
  linear_combination hpq - he

end FLT.Mazur.DifferenceNode

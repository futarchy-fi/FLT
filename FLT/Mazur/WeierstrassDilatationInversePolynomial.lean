/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTangentInverse

/-!
# A polynomial inverse for the full terminal tangent difference

The finite nilpotent inverse is itself a polynomial over the original base.
Its evaluation recovers the horizontal coordinate in every coefficient algebra.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (r : R[X])
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)

/-- A polynomial in the tangent difference, constructed by finite nilpotent inversion. -/
def terminalInversePolynomial : R[X] :=
  terminalInverseX W 0 r I hI hrI ha (0 : R[X]) X

local notation "F" => terminalInversePolynomial W r I hI hrI ha

/-- The inverse polynomial solves the original horizontal equation identically. -/
theorem terminalInversePolynomial_equation :
    F * (C W.a₁ + r.comp F + r.comp F) = X := by
  simpa only [terminalInversePolynomial, algebraMap_eq, comp, map_zero, sub_zero] using
    terminalInverseX_equation W 0 r I hI hrI ha (0 : R[X]) X

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Every polynomial value solves the terminal difference equation over the given base. -/
theorem terminalInversePolynomial_eval_equation (d : S) :
    (F).eval₂ (algebraMap R S) d * (algebraMap R S W.a₁ +
      r.eval₂ (algebraMap R S) ((F).eval₂ (algebraMap R S) d) +
      r.eval₂ (algebraMap R S) ((F).eval₂ (algebraMap R S) d)) = d := by
  have h := congrArg (Polynomial.eval₂ (algebraMap R S) d)
    (terminalInversePolynomial_equation W r I hI hrI ha)
  simpa only [eval₂_mul, eval₂_add, eval₂_C, eval₂_X, eval₂_comp] using h

/-- Polynomial evaluation agrees with the previously constructed full terminal inverse. -/
theorem terminalInversePolynomial_eval (b3 : R) (p q : S) :
    (F).eval₂ (algebraMap R S) (q - p - algebraMap R S b3) =
      terminalInverseX W b3 r I hI hrI ha p q := by
  apply terminalInverseX_unique W b3 r I hI hrI ha p q
  · exact terminalInversePolynomial_eval_equation W r I hI hrI ha _
  · exact terminalInverseX_equation W b3 r I hI hrI ha p q

/-- Substituting the original tangent difference recovers x on the entire terminal chart. -/
theorem terminalInversePolynomial_original (s b3 b4 b6 : R) :
    (F).eval₂ (algebraMap R (Coordinate W s b3 b4 b6))
      (terminalOppositeTangent W s b3 b4 b6 r - terminalSmallTangent W s b3 b4 b6 r -
        algebraMap R (Coordinate W s b3 b4 b6) b3) = x W s b3 b4 b6 := by
  rw [terminalInversePolynomial_eval, terminalInverseX_original]

end FLT.Mazur.WeierstrassDilatation

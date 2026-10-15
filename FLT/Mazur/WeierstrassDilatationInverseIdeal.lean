/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTangentCorrection

/-!
# Arithmetic ideal control for the full terminal inverse polynomial

The recovered horizontal coordinate stays in the arithmetic ideal whenever
the tangent difference does. This controls the exact smoothing correction.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (r : R[X])
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)
  {S : Type*} [CommRing S] [Algebra R S] (d : S)
local notation "f" => algebraMap R S
local notation "T" => Polynomial.eval₂ (algebraMap R S) d
  (terminalInversePolynomial W r I hI hrI ha)

/-- The polynomial inverse preserves the extended arithmetic ideal. -/
theorem terminalInversePolynomial_eval₂_mem (hd : d ∈ I.map (algebraMap R S)) :
    (terminalInversePolynomial W r I hI hrI ha).eval₂ (algebraMap R S) d ∈
      I.map (algebraMap R S) := by
  apply ((I.map f).unit_mul_mem_iff_mem (ha.map f)).mp
  have he : f W.a₁ * T = d - T * (r.eval₂ f T + r.eval₂ f T) := by
    linear_combination terminalInversePolynomial_eval_equation W r I hI hrI ha d
  rw [he]
  have hr := NilpotentPolynomialInverse.eval₂_mem I f r hrI T
  exact (I.map f).sub_mem hd ((I.map f).mul_mem_left _ ((I.map f).add_mem hr hr))

/-- Over the original ring the inverse preserves the original arithmetic ideal. -/
theorem terminalInversePolynomial_eval_mem (z : R) (hz : z ∈ I) :
    (terminalInversePolynomial W r I hI hrI ha).eval z ∈ I := by
  have hz' : z ∈ I.map (algebraMap R R) := by simpa using hz
  simpa using terminalInversePolynomial_eval₂_mem W r I hI hrI ha z hz'

end FLT.Mazur.WeierstrassDilatation

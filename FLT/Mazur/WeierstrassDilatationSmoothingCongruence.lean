/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationInverseIdeal
public import FLT.Mazur.WeierstrassDilatationTerminalNode

/-!
# The constructed terminal smoothing retains the original constant to first order

If the divided linear coefficients vanish in the arithmetic residue, the
computed smoothing differs from the original b6 by an element of I².
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (b3 b4 b6 : R)
  (r : R[X]) (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "F" => terminalInversePolynomial W r I hI hrI ha
local notation "H" => terminalProductCorrection b3 b4 b6 r F
local notation "hH" => terminalProductCorrection_mem b3 b4 b6 r F I h4 h6 hrI
local notation "z" => DifferenceNode.criticalDifference H b3 I hI hH
local notation "a" => DifferenceNode.criticalSlope H b3 I hI hH

include h3 in
/-- The critical tangent difference lies in the original arithmetic ideal. -/
theorem terminalCriticalDifference_mem : z ∈ I := by
  have he : z = -b3 - a - a := by
    linear_combination DifferenceNode.criticalDifference_equation H b3 I hI hH
  rw [he]
  have ha' := DifferenceNode.criticalSlope_mem H b3 I hI hH
  exact I.sub_mem (I.sub_mem (I.neg_mem h3) ha') ha'

include h3 in
/-- The smoothing constant differs from the original b6 only by a quadratic ideal correction. -/
theorem terminalSmoothing_sub_mem_sq :
    terminalSmoothing W b3 b4 b6 r I hI hrI ha h4 h6 - b6 ∈ I ^ 2 := by
  have hz := terminalCriticalDifference_mem W b3 b4 b6 r I hI hrI ha h3 h4 h6
  have ht := terminalInversePolynomial_eval_mem W r I hI hrI ha z hz
  have hr' : r.eval ((F).eval z) ∈ I := by
    simpa only [eval₂_id, Ideal.map_id] using
      NilpotentPolynomialInverse.eval₂_mem I (RingHom.id R) r hrI ((F).eval z)
  have hm : (b4 - b3 * r.eval ((F).eval z)) * (F).eval z ∈ I ^ 2 := by
    simpa only [pow_two] using Ideal.mul_mem_mul (I.sub_mem h4 (I.mul_mem_left _ hr')) ht
  have hs : a ^ 2 ∈ I ^ 2 :=
    Ideal.pow_mem_pow (DifferenceNode.criticalSlope_mem H b3 I hI hH) 2
  convert (I ^ 2).add_mem hm hs using 1
  rw [terminalSmoothing_formula]
  ring

end FLT.Mazur.WeierstrassDilatation

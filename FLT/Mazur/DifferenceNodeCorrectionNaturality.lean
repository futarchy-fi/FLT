/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DifferenceNodeCriticalNaturality
public import FLT.Mazur.DifferenceNodeNormalFactors

/-!
# The entire translated quadratic correction commutes with restriction

All Taylor coefficients from degree two onward are retained. The translation
uses the previously proved compatibility of the actual critical point.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.DifferenceNode
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

/-- Removing the first two Taylor coefficients commutes with every coefficient map. -/
theorem quadraticRemainder_map (h : R[X]) (z : R) :
    (NilpotentPolynomialInverse.quadraticRemainder h z).map f =
      NilpotentPolynomialInverse.quadraticRemainder (h.map f) (f z) := by
  ext n
  simp only [NilpotentPolynomialInverse.quadraticRemainder, coeff_map, coeff_divX]
  rw [← map_taylor, coeff_map]

variable (h : R[X]) (b : R) (I : Ideal R) (hI : IsNilpotent I)
  (J : Ideal S) (hJ : IsNilpotent J) (hf : I ≤ J.comap f) (hh : h ∈ I.map C)
local notation "hhJ" => WeierstrassDilatation.terminalPolynomialIdeal_map f I J hf hh

/-- The complete normal correction, not just its reduction, is compatible with restriction. -/
theorem normalCorrection_map :
    (normalCorrection h b I hI hh).map f = normalCorrection (h.map f) (f b) J hJ hhJ := by
  simp only [normalCorrection]
  rw [quadraticRemainder_map,
    criticalDifference_map f h b I hI J hJ hf hh]

end FLT.Mazur.DifferenceNode

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DifferenceNodeCriticalPoint
public import FLT.Mazur.WeierstrassDilatationTangentRootNaturality

/-!
# The constructed critical point and smoothing commute with coefficient maps

The unique critical difference identifies the actual constructions under
restriction. The slope and smoothing constant then follow by polynomial evaluation.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.DifferenceNode
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (h : R[X]) (b : R) (I : Ideal R) (hI : IsNilpotent I)
  (J : Ideal S) (hJ : IsNilpotent J) (hf : I ≤ J.comap f) (hh : h ∈ I.map C)
local notation "hhJ" => WeierstrassDilatation.terminalPolynomialIdeal_map f I J hf hh

/-- The uniquely constructed critical difference is preserved by coefficient restriction. -/
theorem criticalDifference_map :
    f (criticalDifference h b I hI hh) = criticalDifference (h.map f) (f b) J hJ hhJ := by
  apply criticalDifference_unique (h.map f) (f b) J hJ hhJ
  have he := congrArg f (criticalDifference_equation h b I hI hh)
  simpa only [criticalSlope, derivative_map, eval_map, eval₂_at_apply, map_add, map_neg] using he

/-- The actual critical tangent shift commutes with the same coefficient map. -/
theorem criticalSlope_map :
    f (criticalSlope h b I hI hh) = criticalSlope (h.map f) (f b) J hJ hhJ := by
  simp only [criticalSlope]
  rw [← criticalDifference_map f h b I hI J hJ hf hh]
  simp only [derivative_map, eval_map, eval₂_at_apply]

/-- The full computed smoothing constant commutes with coefficient restriction. -/
theorem smoothingConstant_map :
    f (smoothingConstant h b I hI hh) = smoothingConstant (h.map f) (f b) J hJ hhJ := by
  simp only [smoothingConstant, map_add, map_pow]
  rw [criticalSlope_map f h b I hI J hJ hf hh,
    ← criticalDifference_map f h b I hI J hJ hf hh]
  rw [eval_map, eval₂_at_apply]

end FLT.Mazur.DifferenceNode

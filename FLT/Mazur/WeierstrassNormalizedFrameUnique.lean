/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassFrameNormalization

/-!
# Uniqueness of the normalized frame across different separations

An admissible change carrying one frame (0,0), (0,-d), (-d,0) to
another is identity, even when the two unit parameters initially differ.
Thus normalized coordinates have no residual admissible-coordinate freedom.
-/

@[expose] public section

open WeierstrassCurve

namespace FLT.Mazur.WeierstrassNormalizedFrameUnique

variable {R : Type*} [CommRing R]

/-- A map between two normalized frames is identity and their separations coincide. -/
theorem change_eq_one (C : VariableChange R) (d e : Rˣ)
    (hr : C.r = 0) (ht : C.t = 0)
    (hx : (C.u : R) ^ 2 * -(e : R) + C.r = -(d : R))
    (hy : (C.u : R) ^ 3 * -(e : R) + C.t = -(d : R))
    (hs : (C.u : R) ^ 2 * C.s * -(e : R) + C.t = 0) : C = 1 ∧ d = e := by
  have hx' : (C.u : R) ^ 2 * (e : R) = d := by
    simpa only [hr, add_zero, mul_neg, neg_inj] using hx
  have hy' : (C.u : R) ^ 3 * (e : R) = d := by
    simpa only [ht, add_zero, mul_neg, neg_inj] using hy
  have hu : (C.u : R) = 1 := by
    apply sub_eq_zero.mp
    apply ((C.u.isUnit.pow 2).mul e.isUnit).mul_right_eq_zero.mp
    linear_combination hy' - hx'
  have hs' : C.s = 0 := by
    apply e.isUnit.mul_right_eq_zero.mp
    have he : -C.s * (e : R) = 0 := by
      simpa only [hu, ht, one_pow, one_mul, add_zero, mul_neg, neg_mul] using hs
    linear_combination -he
  constructor
  · exact VariableChange.ext (Units.ext hu) hr hs' ht
  · apply Units.ext
    simpa only [hu, one_pow, one_mul] using hx'.symm

/-- Two normalized equations related through their normalized markings are the same equation. -/
theorem equation_eq (W V : WeierstrassCurve R) (C : VariableChange R) (d e : Rˣ)
    (hW : C • W = V) (hr : C.r = 0) (ht : C.t = 0)
    (hx : (C.u : R) ^ 2 * -(e : R) + C.r = -(d : R))
    (hy : (C.u : R) ^ 3 * -(e : R) + C.t = -(d : R))
    (hs : (C.u : R) ^ 2 * C.s * -(e : R) + C.t = 0) : W = V := by
  obtain ⟨hC, _⟩ := change_eq_one C d e hr ht hx hy hs
  simpa only [hC, one_smul] using hW

end FLT.Mazur.WeierstrassNormalizedFrameUnique

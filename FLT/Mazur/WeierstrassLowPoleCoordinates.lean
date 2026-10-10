/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassNormalFormPoles
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

/-!
# The original pole-two and pole-three spaces

Every affine function with pole bound two is a linear combination of 1 and x.
Bound three adds precisely y. These statements hold over every coefficient
ring, including nonreduced rings and characteristic three.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Bound two in normal form leaves a linear x polynomial and no y polynomial. -/
theorem affineNormalForm_pole_two (p q : R[X])
    (h : HasOriginPoleBound W (affineNormalForm W p q) 2) :
    p.natDegree ≤ 1 ∧ q = 0 := by
  obtain ⟨hp, hq⟩ := (affineNormalForm_pole_iff W p q 2).mp h
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    exact (hp i).resolve_right (by omega)
  · ext i
    simpa using (hq i).resolve_right (by omega)

/-- Bound three in normal form leaves a linear x polynomial and a constant y polynomial. -/
theorem affineNormalForm_pole_three (p q : R[X])
    (h : HasOriginPoleBound W (affineNormalForm W p q) 3) :
    p.natDegree ≤ 1 ∧ q.natDegree ≤ 0 := by
  obtain ⟨hp, hq⟩ := (affineNormalForm_pole_iff W p q 3).mp h
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    exact (hp i).resolve_right (by omega)
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    exact (hq i).resolve_right (by omega)

/-- The actual pole-two space is exactly the span of the original constant and x coordinates. -/
theorem originPole_two_iff (a : Coordinate W 2) :
    HasOriginPoleBound W a 2 ↔ ∃ r s : R,
      a = algebraMap R _ r + algebraMap R _ s * coord W 2 0 := by
  constructor
  · intro h
    obtain ⟨p, q, rfl⟩ := exists_affineNormalForm W a
    obtain ⟨hp, rfl⟩ := affineNormalForm_pole_two W p q h
    refine ⟨p.coeff 0, p.coeff 1, ?_⟩
    have he := eq_X_add_C_of_natDegree_le_one hp
    conv_lhs => rw [affineNormalForm, he]
    simp [add_comm]
  · rintro ⟨r, s, rfl⟩
    apply originPole_add
    · exact originPole_mono W _ (by decide) (originPole_constant W r)
    · simpa using originPole_mul W _ _ 0 2 (originPole_constant W s) (originPole_x W)

/-- The actual pole-three space is exactly the span of the original 1, x, and y coordinates. -/
theorem originPole_three_iff (a : Coordinate W 2) :
    HasOriginPoleBound W a 3 ↔ ∃ r s t : R,
      a = algebraMap R _ r + algebraMap R _ s * coord W 2 0 +
        algebraMap R _ t * coord W 2 1 := by
  constructor
  · intro h
    obtain ⟨p, q, rfl⟩ := exists_affineNormalForm W a
    obtain ⟨hp, hq⟩ := affineNormalForm_pole_three W p q h
    refine ⟨p.coeff 0, p.coeff 1, q.coeff 0, ?_⟩
    have hep := eq_X_add_C_of_natDegree_le_one hp
    have heq := eq_C_of_natDegree_le_zero hq
    conv_lhs => rw [affineNormalForm, hep, heq]
    simp [add_comm]
  · rintro ⟨r, s, t, rfl⟩
    apply originPole_add
    · exact originPole_mono W _ (by decide) ((originPole_two_iff W _).mpr ⟨r, s, rfl⟩)
    · simpa using originPole_mul W _ _ 0 3 (originPole_constant W t) (originPole_y W)

end FLT.Mazur.WeierstrassIntegralChart

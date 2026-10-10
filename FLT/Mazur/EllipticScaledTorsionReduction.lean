/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSmallRamificationSpecialization

/-!
# The reduction obstruction for a positive weighted scaling

A nonzero p-torsion point on the scaled integral equation has integral
coordinates under small ramification. Multiplying those coordinates by u² and
u³, with u in the maximal ideal, lands at the singular origin of the original
normalized equation. This is the coordinate obstruction needed for S2b descent.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Weighted scaling by a nonunit sends integral coordinates to the singular origin. -/
theorem not_smoothReduction_weighted_integral
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (u : A) (hu : u ∈ maximalIdeal A) (x y : A)
    (h : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((u : K) ^ 2 * x) ((u : K) ^ 3 * y)) :
    ¬ SmoothReduction A W (Affine.Point.some _ _ h).toProjective := by
  have hu0 := (residue_eq_zero_iff _).mpr hu
  have h30 := (residue_eq_zero_iff _).mpr h3
  have h40 := (residue_eq_zero_iff _).mpr h4
  have hs := smoothReduction_affine_iff A W (u ^ 2 * x) (u ^ 3 * y) h
  push_cast at hs
  rw [hs]
  simp only [map_mul, map_pow, hu0, zero_pow (by decide : 2 ≠ 0), zero_mul,
    zero_pow (by decide : 3 ≠ 0), Affine.nonsingular_zero, map_a₃, map_a₄,
    h30, h40, ne_self_iff_false, or_self, and_false, not_false_eq_true]

variable [IsAdicComplete (maximalIdeal A) A] [IsDiscreteValuationRing A] [DecidableEq K]

/-- Actual prime torsion cannot scale positively into the original smooth-reduction locus. -/
theorem not_smoothReduction_weighted_prime_torsion
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (U : WeierstrassCurve A) (p : ℕ) [Fact p.Prime]
    (hp0 : (p : A) ≠ 0) (he : RaynaudParameters.order (p : A) < p - 1)
    (u : A) (hu : u ∈ maximalIdeal A) {x y : K}
    (hU : (U.map (algebraMap A K)).toAffine.Nonsingular x y)
    (hP : p • Affine.Point.some x y hU = 0)
    (hW : (W.map (algebraMap A K)).toAffine.Nonsingular
      ((u : K) ^ 2 * x) ((u : K) ^ 3 * y)) :
    ¬ SmoothReduction A W (Affine.Point.some _ _ hW).toProjective := by
  obtain ⟨hx, hy⟩ := affine_prime_torsion_coordinates_integral A U p hp0 he hU hP
  exact not_smoothReduction_weighted_integral A W h3 h4 u hu ⟨x, hx⟩ ⟨y, hy⟩ hW

end FLT.Mazur

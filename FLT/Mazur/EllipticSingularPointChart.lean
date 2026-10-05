/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNormalizedSingularity
public import FLT.Mazur.EllipticComponentQuotient

/-!
# Integral affine representatives of singularly reducing points

For a normalized singular special fiber, every point outside E₀ is represented
by integral affine coordinates in the maximal ideal. This chart does not
require any finite-depth nodal packet or additive classification.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- A point outside E₀ has an actual affine representative above the normalized singular origin. -/
theorem exists_singular_integral_affine
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (h6 : W.a₆ ∈ maximalIdeal A)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : ¬ SmoothReduction A W P) :
    ∃ (x y : A) (h : (W.map (algebraMap A K)).toAffine.Nonsingular (x : K) (y : K)),
      x ∈ maximalIdeal A ∧ y ∈ maximalIdeal A ∧ P = (Affine.Point.some _ _ h).toProjective := by
  classical
  obtain ⟨p, rfl⟩ := (Projective.Point.toAffineAddEquiv
    (W.map (algebraMap A K)).toProjective).symm.surjective P
  cases p with
  | zero => exact (hP (smoothReduction_zero A W)).elim
  | some x y h =>
    have hi : x ∈ A ∧ y ∈ A := by
      by_contra hn
      exact hP (smoothReduction_of_nonintegral A W h hn)
    let x' : A := ⟨x, hi.1⟩
    let y' : A := ⟨y, hi.2⟩
    have he : W.toAffine.Equation x' y' :=
      (W.toAffine.map_equation (IsFractionRing.injective A K) x' y').mp h.1
    have hr : residue A x' = 0 ∧ residue A y' = 0 := by
      by_contra hn
      apply hP
      apply (smoothReduction_affine_iff A W x' y' h).mpr
      exact (normalized_nonsingular_iff (W.map (residue A))
        ((residue_eq_zero_iff _).mpr h3) ((residue_eq_zero_iff _).mpr h4)
        ((residue_eq_zero_iff _).mpr h6) (he.map (residue A))).mpr hn
    exact ⟨x', y', h, (residue_eq_zero_iff _).mp hr.1, (residue_eq_zero_iff _).mp hr.2, rfl⟩

end FLT.Mazur

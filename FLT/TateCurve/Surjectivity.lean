/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.Points

/-!
# Reducing Tate surjectivity to one coordinate

An elliptic curve point is determined up to negation by its abscissa. Since
inversion of the Tate parameter argument gives point negation, it suffices to
solve the scalar equation `tateX u q = x` for each abscissa on the curve.
This file proves the reduction; existence of such a solution remains an
analytic theorem.
-/

@[expose] public section

open ValuativeRel WeierstrassCurve.Affine

namespace TateCurve

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Hitting every abscissa on the curve suffices for surjectivity of the Tate point map. -/
theorem uniformizationPoint_surjective_of_tateX (q : Kˣ)
    (hq : valuation K (q : K) < 1)
    (hx : ∀ x y : K, (WeierstrassCurve.tateCurve (q : K)).toAffine.Nonsingular x y →
      ∃ u : Kˣ, u ∉ Subgroup.zpowers q ∧ tateX (u : K) (q : K) = x) :
    Function.Surjective (uniformizationPoint q hq) := by
  classical
  intro P
  cases P with
  | zero => exact ⟨1, (uniformizationPoint_eq_zero q 1 hq).mpr (Subgroup.one_mem _)⟩
  | some x y h =>
    obtain ⟨u, hu, hxu⟩ := hx x y h
    have hpoint : uniformizationPoint q hq u =
        Point.some _ _ (tateCoordinates_nonsingular q u hq hu) := by
      simp only [uniformizationPoint, dite_eq_right hu]
    rcases (Point.X_eq_iff (h₁ := tateCoordinates_nonsingular q u hq hu)
      (h₂ := h)).mp hxu with hp | hp
    · exact ⟨u, hpoint.trans hp⟩
    · refine ⟨u⁻¹, ?_⟩
      rw [uniformizationPoint_inv, hpoint, hp, neg_neg]

/-- Surjectivity of the quotient map is equivalent to hitting every affine abscissa. -/
theorem quotientPoint_surjective_iff_tateX (q : Kˣ)
    (hq : valuation K (q : K) < 1) :
    Function.Surjective (quotientPoint q hq) ↔
      ∀ x y : K, (WeierstrassCurve.tateCurve (q : K)).toAffine.Nonsingular x y →
        ∃ u : Kˣ, u ∉ Subgroup.zpowers q ∧ tateX (u : K) (q : K) = x := by
  classical
  constructor
  · intro h x y hxy
    obtain ⟨a, ha⟩ := h (Point.some x y hxy)
    induction a using Quotient.inductionOn with
    | h u =>
      rw [quotientPoint_mk] at ha
      have hu : u ∉ Subgroup.zpowers q := by
        intro hu
        have hz := (uniformizationPoint_eq_zero q u hq).mpr hu
        rw [ha] at hz
        exact Point.some_ne_zero hxy hz
      refine ⟨u, hu, ?_⟩
      simp only [uniformizationPoint, dite_eq_right hu, Point.some.injEq] at ha
      exact ha.1
  · intro hx P
    obtain ⟨u, hu⟩ := uniformizationPoint_surjective_of_tateX q hq hx P
    exact ⟨u, hu⟩

end TateCurve

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.TateInertia
public import FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.SplitMultiplicativeReduction
public import Mathlib.RingTheory.Valuation.Integral

/-!
# Inertia at multiplicative reduction

Integral quadratic twisting parameters with unit discriminant split multiplicative
reduction, including in residue characteristic two.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine
open Polynomial IsLocalRing

universe u

namespace WeierstrassCurve

/-- A multiplicative equation admits integral twisting parameters with unit
discriminant for which the explicit twisted integral equation is split multiplicative. -/
theorem exists_split_twist_parameters {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (E : WeierstrassCurve K) [E.HasMultiplicativeReduction R] :
    ∃ t n : R, IsUnit (t ^ 2 - 4 * n) ∧
      (((E.integralModel R).quadraticTwistOf t n).baseChange K).HasSplitMultiplicativeReduction
        R := by
  let W := E.integralModel R
  let c := residue R W.c₄
  have hc : c ≠ 0 := residue_integralModel_c₄_ne_zero E R
  let b := residue R (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)
  obtain ⟨n, hn⟩ := residue_surjective (-(b / c))
  let t := -W.a₁
  have hA : residue R W.c₄ * residue R t + residue R (W.a₁ * W.c₄) = 0 := by
    simp only [t, map_neg, map_mul]
    ring
  have hB : residue R W.c₄ * residue R n + b = 0 := by
    rw [hn]
    dsimp [c] at *
    field_simp
    ring
  have hkey := residue_c₄_mul_residue_eq_neg_c₆ E R t n hA hB
  have hD : residue R (t ^ 2 - 4 * n) ≠ 0 := by
    intro h
    rw [h, mul_zero, eq_comm, neg_eq_zero] at hkey
    exact residue_integralModel_c₆_ne_zero E R hkey
  let :=  hasMultiplicativeReduction_baseChange_quadraticTwistOf E R t n hD
  exact ⟨t, n, (residue_ne_zero_iff_isUnit _).mp hD,
    hasSplitMultiplicativeReduction_quadraticTwistOf_of_residue E R t n hA hB⟩

end WeierstrassCurve

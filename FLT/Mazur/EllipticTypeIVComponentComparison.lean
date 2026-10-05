/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticTypeIVCoordinates
public import FLT.Mazur.EllipticTypeIVAddition

/-!
# Comparing actual components in the type IV branch

Different divided y-labels have smooth sum. Equal labels have smooth
difference, because the residual quadratic has distinct roots. Consequently
any two points above the cusp give equal or opposite component classes.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- Coordinate witnesses with distinct residual labels have smooth sum. -/
theorem TypeIVCoordinates.smooth_add_of_distinct
    (v : TypeIVCoordinates A W π P) (w : TypeIVCoordinates A W π Q)
    (hπ : π ≠ 0) (hπm : π ∈ maximalIdeal A)
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (h6 : W.a₆ ∈ maximalIdeal A) (hy : residue A v.y ≠ residue A w.y) :
    SmoothReduction A W (P + Q) := by
  classical
  have hs := smoothReduction_add_of_typeIV_distinct A W hπ hπm v.x v.y w.x w.y
    v.nonsingular w.nonsingular h1 h2 h3 h4 h6 hy
  rw [toProjective_add] at hs
  simpa only [v.represents, w.represents] using hs

/-- Actual component classes above the type IV cusp are equal or opposite. -/
theorem TypeIVCoordinates.component_eq_or_neg
    (v : TypeIVCoordinates A W π P) (w : TypeIVCoordinates A W π Q)
    (hπ : π ≠ 0) (hπm : π ∈ maximalIdeal A) (e3 e4 e6 : A)
    (h1 : W.a₁ ∈ maximalIdeal A) (h2 : W.a₂ ∈ maximalIdeal A)
    (h4m : e4 ∈ maximalIdeal A)
    (h3 : W.a₃ = π * e3) (h4 : W.a₄ = π * e4) (h6 : W.a₆ = π ^ 2 * e6)
    (hb6 : W.b₆ ∉ maximalIdeal A ^ 3) :
    ellipticComponentHom A W P = ellipticComponentHom A W Q ∨
      ellipticComponentHom A W P = -ellipticComponentHom A W Q := by
  have h3m : W.a₃ ∈ maximalIdeal A := h3 ▸ (maximalIdeal A).mul_mem_right _ hπm
  have h4' : W.a₄ ∈ maximalIdeal A := h4 ▸ (maximalIdeal A).mul_mem_right _ hπm
  have h6m : W.a₆ ∈ maximalIdeal A := by
    rw [h6, pow_two, mul_assoc]
    exact (maximalIdeal A).mul_mem_right _ hπm
  by_cases he : residue A v.y = residue A w.y
  · left
    apply (ellipticComponentHom_eq_iff A W P Q).mpr
    rw [sub_eq_add_neg]
    apply v.smooth_add_of_distinct (w.neg e3 h3) hπ hπm h1 h2 h3m h4' h6m
    rw [w.neg_residue e3 h3 h1, he]
    exact typeIV_root_ne_opposite
      (typeIV_scaled_residue W hπ hπm w.x w.y e3 e4 e6 h1 h2 h4m h3 h4 h6 w.equation)
      (typeIV_residue_discriminant_ne_zero W hπm e3 e6 h3 h6 hb6)
  · right
    apply eq_neg_of_add_eq_zero_left
    rw [← map_add, ellipticComponentHom_eq_zero]
    exact v.smooth_add_of_distinct w hπ hπm h1 h2 h3m h4' h6m he

end FLT.Mazur

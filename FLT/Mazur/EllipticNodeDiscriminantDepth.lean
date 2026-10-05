/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Discriminant depth at a normalized node

Modulo an ideal containing a₃ and a₄, Δ is a₆ times −b₂³−432a₆.
For nodal coefficients this factor is a unit, including in characteristics
2 and 3. Thus sufficiently deep a₃,a₄ identify the ideal-adic depth of a₆
with that of Δ; this is a coefficient calculation, not a component count.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Modulo a₃ and a₄, the discriminant factors through a₆. -/
theorem node_discriminant_congr (I : Ideal R) (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∈ I) :
    W.Δ - W.a₆ * (-W.b₂ ^ 3 - 432 * W.a₆) ∈ I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h3' := Ideal.Quotient.eq_zero_iff_mem.mpr h3
  have h4' := Ideal.Quotient.eq_zero_iff_mem.mpr h4
  simp only [Δ, b₈, b₆, b₄, b₂, map_sub, map_add, map_mul, map_pow, map_neg,
    map_ofNat, h3', h4']
  ring

/-- The a₆ factor in the nodal discriminant is a unit in every residue characteristic. -/
theorem isUnit_node_discriminant_factor [IsLocalRing R]
    (h1 : IsUnit W.a₁) (h2 : W.a₂ ∈ maximalIdeal R) (h6 : W.a₆ ∈ maximalIdeal R) :
    IsUnit (-W.b₂ ^ 3 - 432 * W.a₆) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  have h1' := (residue_ne_zero_iff_isUnit _).mpr h1
  have h2' := (residue_eq_zero_iff _).mpr h2
  have h6' := (residue_eq_zero_iff _).mpr h6
  simpa [b₂, h2', h6'] using neg_ne_zero.mpr (pow_ne_zero 3 (pow_ne_zero 2 h1'))

/-- At a normalized node, sufficiently deep a₃,a₄ make Δ and a₆ have the same depth. -/
theorem node_discriminant_mem_pow_iff [IsLocalRing R]
    (h1 : IsUnit W.a₁) (h2 : W.a₂ ∈ maximalIdeal R) (h6 : W.a₆ ∈ maximalIdeal R)
    (n : ℕ) (h3 : W.a₃ ∈ maximalIdeal R ^ n) (h4 : W.a₄ ∈ maximalIdeal R ^ n) :
    W.Δ ∈ maximalIdeal R ^ n ↔ W.a₆ ∈ maximalIdeal R ^ n := by
  have hcon := node_discriminant_congr W (maximalIdeal R ^ n) h3 h4
  have hu := isUnit_node_discriminant_factor W h1 h2 h6
  constructor
  · intro hd
    apply ((maximalIdeal R ^ n).mul_unit_mem_iff_mem hu).mp
    convert (maximalIdeal R ^ n).sub_mem hd hcon using 1
    ring
  · intro ha
    have hm := (maximalIdeal R ^ n).mul_mem_right (-W.b₂ ^ 3 - 432 * W.a₆) ha
    convert (maximalIdeal R ^ n).add_mem hcon hm using 1
    ring

/-- The exact discriminant depth also determines the exact a₆ depth. -/
theorem node_a₆_exact_depth [IsLocalRing R]
    (h1 : IsUnit W.a₁) (h2 : W.a₂ ∈ maximalIdeal R) (h6 : W.a₆ ∈ maximalIdeal R)
    (n : ℕ) (h3 : W.a₃ ∈ maximalIdeal R ^ (n + 1))
    (h4 : W.a₄ ∈ maximalIdeal R ^ (n + 1))
    (hd : W.Δ ∈ maximalIdeal R ^ n) (hd' : W.Δ ∉ maximalIdeal R ^ (n + 1)) :
    W.a₆ ∈ maximalIdeal R ^ n ∧ W.a₆ ∉ maximalIdeal R ^ (n + 1) := by
  exact ⟨(node_discriminant_mem_pow_iff W h1 h2 h6 n
    (Ideal.pow_le_pow_right (by omega) h3) (Ideal.pow_le_pow_right (by omega) h4)).mp hd,
    fun h => hd' ((node_discriminant_mem_pow_iff W h1 h2 h6 (n + 1) h3 h4).mpr h)⟩

end FLT.Mazur

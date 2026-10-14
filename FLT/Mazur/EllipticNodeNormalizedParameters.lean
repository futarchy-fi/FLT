/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeMiddleSumLaurentCharacter

/-!
# Normalized parameters and the original wraparound coefficient

Divide the positive tangent by a₁³ and take minus a₁³ over the negative
tangent. These oriented parameters invert under point negation. Their
transition at the midpoint retains the original coefficient -c₆/a₁⁶;
no root or replacement coefficient ring is chosen.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} {P : (W.map (algebraMap A K)).toProjective.Point}

/-- The positive oriented parameter of an original primitive point. -/
def nodePositiveParameter (v : NodePointCoordinates A W π P) : ResidueField A :=
  residue A (v.b + W.a₁ * v.a) / residue A W.a₁ ^ 3

/-- The negative oriented parameter, compatible with inversion of the positive one. -/
def nodeNegativeParameter (v : NodePointCoordinates A W π P) : ResidueField A :=
  -(residue A W.a₁ ^ 3) / residue A v.b

/-- The coefficient relating an increase by the full component period. -/
def nodeWrapParameter (W : WeierstrassCurve A) (c₆ : A) : ResidueField A :=
  -residue A c₆ / (residue A W.a₁ ^ 3) ^ 2

variable (D : SplitNodeDepth W π n)

include D

/-- The constant coefficient at its exact depth is a unit. -/
theorem node_leading_constant_isUnit (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) : IsUnit c₆ := by
  by_contra hm
  apply D.a₆_not_mem
  rw [h6, pow_succ]
  exact Ideal.mul_mem_mul
    (Ideal.pow_mem_pow (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π) n) hm

/-- The original wraparound coefficient is nonzero. -/
theorem nodeWrapParameter_ne_zero (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) :
    nodeWrapParameter W c₆ ≠ 0 := by
  exact div_ne_zero (neg_ne_zero.mpr
    ((residue_ne_zero_iff_isUnit _).mpr (node_leading_constant_isUnit D c₆ h6)))
    (pow_ne_zero _ (pow_ne_zero _ ((residue_ne_zero_iff_isUnit _).mpr D.a₁_unit)))

/-- A unit positive tangent gives a nonzero normalized parameter. -/
theorem nodePositiveParameter_ne_zero (v : NodePointCoordinates A W π P)
    (hv : IsUnit (v.b + W.a₁ * v.a)) : nodePositiveParameter v ≠ 0 :=
  div_ne_zero ((residue_ne_zero_iff_isUnit _).mpr hv)
    (pow_ne_zero _ ((residue_ne_zero_iff_isUnit _).mpr D.a₁_unit))

/-- A unit negative tangent gives a nonzero normalized parameter. -/
theorem nodeNegativeParameter_ne_zero (v : NodePointCoordinates A W π P)
    (hv : IsUnit v.b) : nodeNegativeParameter v ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr
    (pow_ne_zero _ ((residue_ne_zero_iff_isUnit _).mpr D.a₁_unit)))
    ((residue_ne_zero_iff_isUnit _).mpr hv)

/-- The two midpoint parameterizations differ by exactly the original wraparound coefficient. -/
theorem node_middle_parameter_transition (v : NodePointCoordinates A W π P)
    (hm : 2 * v.depth = n) (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) :
    nodePositiveParameter v = nodeWrapParameter W c₆ * nodeNegativeParameter v := by
  have hα := (residue_ne_zero_iff_isUnit _).mpr D.a₁_unit
  have hb := (residue_ne_zero_iff_isUnit _).mpr (v.units_of_middle D hm).1
  have hc := node_middle_tangent_character D v hm c₆ h6
  dsimp [nodePositiveParameter, nodeNegativeParameter, nodeWrapParameter]
  field_simp
  linear_combination hc

/-- Negating the original point exchanges the two oriented parameters by inversion. -/
theorem node_inverse_parameter (v : NodePointCoordinates A W π P)
    (w : NodePointCoordinates A W π (-P)) (hv : v.depth ≤ n / 2) :
    nodeNegativeParameter w = (nodePositiveParameter v)⁻¹ := by
  have hb := (node_inverse_coordinate_residues D v w hv).2.2
  simp only [nodeNegativeParameter, nodePositiveParameter, hb, neg_div_neg_eq, inv_div]

/-- Negation also exchanges the negative parameter with the inverse positive parameter. -/
theorem node_inverse_positive_parameter (v : NodePointCoordinates A W π P)
    (w : NodePointCoordinates A W π (-P)) (hv : v.depth ≤ n / 2) :
    nodePositiveParameter w = (nodeNegativeParameter v)⁻¹ := by
  have hb := node_inverse_other_residue D v w hv
  simp only [nodePositiveParameter, nodeNegativeParameter, hb, neg_div, inv_neg, inv_div]

/-- Normalization preserves equality of positive tangent residues. -/
theorem nodePositiveParameter_eq_iff
    {Q : (W.map (algebraMap A K)).toProjective.Point}
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q) :
    nodePositiveParameter v = nodePositiveParameter w ↔
      residue A (v.b + W.a₁ * v.a) = residue A (w.b + W.a₁ * w.a) :=
  div_left_inj' (pow_ne_zero _ ((residue_ne_zero_iff_isUnit _).mpr D.a₁_unit))

/-- Normalization preserves equality of negative tangent residues. -/
theorem nodeNegativeParameter_eq_iff
    {Q : (W.map (algebraMap A K)).toProjective.Point}
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q) :
    nodeNegativeParameter v = nodeNegativeParameter w ↔ residue A v.b = residue A w.b := by
  have hn := neg_ne_zero.mpr
    (pow_ne_zero 3 ((residue_ne_zero_iff_isUnit _).mpr D.a₁_unit))
  simp only [nodeNegativeParameter, div_eq_mul_inv]
  constructor
  · intro he
    exact inv_injective (mul_left_cancel₀ hn he)
  · intro he
    rw [he]

end FLT.Mazur

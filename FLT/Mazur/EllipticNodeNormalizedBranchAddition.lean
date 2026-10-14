/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeNormalizedParameters
public import FLT.Mazur.EllipticNodeSecondSumLaurentCharacter

/-!
# Normalized multiplication on the two strict branches

The original coefficient factors disappear in oriented normalized parameters.
Strict sums multiply directly. Passing across the opposite branch retains
one explicit copy of the original wraparound coefficient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}
  (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
  (u : NodePointCoordinates A W π (P + Q))

include D

/-- Positive strict sums multiply their normalized original parameters. -/
theorem node_positive_parameter_add
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n) (hu : 2 * u.depth < n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A)
    (hf : u.b ∈ maximalIdeal A) :
    nodePositiveParameter v * nodePositiveParameter w = nodePositiveParameter u := by
  have hc := node_first_sum_laurent_character D v w u hv0 hw0 hv hw hu hb hd hf
  have hα := (residue_ne_zero_iff_isUnit _).mpr D.a₁_unit
  dsimp [nodePositiveParameter]
  rw [div_mul_div_comm, hc]
  field_simp

/-- Negative strict sums multiply their normalized original parameters. -/
theorem node_negative_parameter_add
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth) (hu0 : 0 < u.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n) (hu : 2 * u.depth < n)
    (hb : IsUnit v.b) (hd : IsUnit w.b) (hf : IsUnit u.b) :
    nodeNegativeParameter v * nodeNegativeParameter w = nodeNegativeParameter u := by
  have hc := (node_second_sum_laurent_character D v w u hv0 hw0 hu0 hv hw hu hb hd hf).2
  have hα := (residue_ne_zero_iff_isUnit _).mpr D.a₁_unit
  have hbu := (residue_ne_zero_iff_isUnit _).mpr hf
  dsimp [nodeNegativeParameter]
  rw [div_mul_div_comm, hc]
  field_simp

/-- A positive sum crossing to the negative branch retains exactly the wraparound factor. -/
theorem node_positive_parameter_wrap
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth) (hu0 : 0 < u.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n) (hu : 2 * u.depth < n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) (hf : IsUnit u.b)
    (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) :
    nodePositiveParameter v * nodePositiveParameter w =
      nodeWrapParameter W c₆ * nodeNegativeParameter u := by
  have hc := (node_wrapped_sum_character D v w u hv0 hw0 hv hw hu0 hu hb hd hf c₆ h6).2
  have hα := (residue_ne_zero_iff_isUnit _).mpr D.a₁_unit
  have hbu := (residue_ne_zero_iff_isUnit _).mpr hf
  dsimp [nodePositiveParameter, nodeNegativeParameter, nodeWrapParameter]
  field_simp
  linear_combination hc

/-- The negative wraparound law uses the same original coefficient. -/
theorem node_negative_parameter_wrap
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth) (hu0 : 0 < u.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n) (hu : 2 * u.depth < n)
    (hb : IsUnit v.b) (hd : IsUnit w.b) (hf : u.b ∈ maximalIdeal A)
    (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) :
    nodeWrapParameter W c₆ * (nodeNegativeParameter v * nodeNegativeParameter w) =
      nodePositiveParameter u := by
  have hc := (node_second_wrapped_sum_character D v w u hv0 hw0 hu0 hv hw hu hb hd hf
    c₆ h6).2
  have hα := (residue_ne_zero_iff_isUnit _).mpr D.a₁_unit
  have hbv := (residue_ne_zero_iff_isUnit _).mpr hb
  have hbw := (residue_ne_zero_iff_isUnit _).mpr hd
  dsimp [nodePositiveParameter, nodeNegativeParameter, nodeWrapParameter]
  field_simp
  linear_combination -hc

end FLT.Mazur

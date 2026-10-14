/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeNormalizedBranchAddition
public import FLT.Mazur.EllipticNodeMiddleSmoothCharacter

/-!
# Normalized multiplication through the midpoint and identity component

The midpoint transition reconciles its two tangent parameters. Sums entering
or leaving this component retain precisely the original period coefficient;
opposite strict inputs multiply to the actual original smooth character.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}
  (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)

include D

/-- First-branch inputs multiply to the positive parameter of an actual midpoint output. -/
theorem node_positive_parameter_middle
    (u : NodePointCoordinates A W π (P + Q))
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n) (hm : 2 * u.depth = n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A)
    (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) :
    nodePositiveParameter v * nodePositiveParameter w = nodePositiveParameter u := by
  have hc := node_first_middle_sum_character D v w u hv0 hw0 hv hw hm hb hd c₆ h6
  have ht := node_middle_tangent_character D u hm c₆ h6
  have hbu := (residue_ne_zero_iff_isUnit _).mpr (u.units_of_middle D hm).1
  have he : residue A (v.b + W.a₁ * v.a) * residue A (w.b + W.a₁ * w.a) =
      residue A W.a₁ ^ 3 * residue A (u.b + W.a₁ * u.a) := by
    apply mul_right_cancel₀ hbu
    linear_combination hc - residue A W.a₁ ^ 3 * ht
  have hα := (residue_ne_zero_iff_isUnit _).mpr D.a₁_unit
  dsimp [nodePositiveParameter]
  rw [div_mul_div_comm, he]
  field_simp

/-- Negative inputs multiply to the negative parameter at the actual midpoint. -/
theorem node_negative_parameter_middle
    (u : NodePointCoordinates A W π (P + Q))
    (hv0 : 0 < v.depth) (hw0 : 0 < w.depth)
    (hv : 2 * v.depth < n) (hw : 2 * w.depth < n) (hm : 2 * u.depth = n)
    (hb : IsUnit v.b) (hd : IsUnit w.b)
    (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) :
    nodeNegativeParameter v * nodeNegativeParameter w = nodeNegativeParameter u := by
  have hc := (node_second_middle_sum_character D v w u hv0 hw0 hv hw hm hb hd c₆ h6).2
  have hα := (residue_ne_zero_iff_isUnit _).mpr D.a₁_unit
  have hbu := (residue_ne_zero_iff_isUnit _).mpr (u.units_of_middle D hm).1
  dsimp [nodeNegativeParameter]
  rw [div_mul_div_comm, hc]
  field_simp

variable [DecidableEq (ResidueField A)]

/-- Opposite strict parameters multiply to the actual smooth character of their sum. -/
theorem node_opposite_parameter_smooth
    (hk : 0 < v.depth) (hn : 2 * v.depth < n) (he : v.depth = w.depth)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    nodePositiveParameter v * nodeNegativeParameter w =
      (Additive.toMul (splitDepthSmoothCharacter D
        ⟨P + Q, v.smooth_add_of_opposite D w hk hn he hb hd⟩)).val := by
  have hc := node_opposite_smooth_character D v w hk hn he hb hd
  have hα := (residue_ne_zero_iff_isUnit _).mpr D.a₁_unit
  have hbw := (residue_ne_zero_iff_isUnit _).mpr hd
  dsimp [nodePositiveParameter, nodeNegativeParameter]
  field_simp
  linear_combination -hc

/-- Two positive midpoint parameters multiply to the period times the actual smooth character. -/
theorem node_middle_parameter_smooth
    (hv : 2 * v.depth = n) (hw : 2 * w.depth = n)
    (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) :
    nodePositiveParameter v * nodePositiveParameter w = nodeWrapParameter W c₆ *
      (Additive.toMul (splitDepthSmoothCharacter D
        ⟨P + Q, v.smooth_add_of_middle D w hv hw⟩)).val := by
  have hc := node_middle_smooth_character D v w hv hw
  have ht := node_middle_tangent_character D v hv c₆ h6
  have he : residue A (v.b + W.a₁ * v.a) * residue A (w.b + W.a₁ * w.a) =
      -residue A c₆ * (Additive.toMul (splitDepthSmoothCharacter D
        ⟨P + Q, v.smooth_add_of_middle D w hv hw⟩)).val := by
    linear_combination residue A (v.b + W.a₁ * v.a) * hc -
      (Additive.toMul (splitDepthSmoothCharacter D
        ⟨P + Q, v.smooth_add_of_middle D w hv hw⟩)).val * ht
  dsimp [nodePositiveParameter, nodeWrapParameter]
  rw [div_mul_div_comm, he]
  ring

end FLT.Mazur

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeNormalizedParameters
public import FLT.Mazur.EllipticNodeReflectedMixedCharacter

/-!
# Normalized multiplication for unequal opposite depths

Both orientations of a mixed sum multiply their original normalized
parameters. The deeper input may be a midpoint point; its two parameter
conventions are related by the explicit original period coefficient.
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

/-- A shallower positive input and deeper negative input multiply to the negative output. -/
theorem node_positive_negative_parameter_add
    (hk : 0 < v.depth) (hkw : v.depth < w.depth) (hw : w.depth ≤ n / 2)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    nodePositiveParameter v * nodeNegativeParameter w = nodeNegativeParameter u := by
  have hc := node_add_first_unit_character D v w u hk hkw hw hb hd
  have hα := (residue_ne_zero_iff_isUnit _).mpr D.a₁_unit
  have hbw := (residue_ne_zero_iff_isUnit _).mpr hd
  have hbu : residue A u.b ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hc
    exact (mul_ne_zero (pow_ne_zero _ hα) hbw) hc.symm
  dsimp [nodePositiveParameter, nodeNegativeParameter]
  field_simp
  linear_combination -hc

/-- The reflected mixed sum multiplies to the positive output parameter. -/
theorem node_negative_positive_parameter_add
    (hk : 0 < v.depth) (hkw : v.depth < w.depth) (hw : w.depth ≤ n / 2)
    (hb : IsUnit v.b) (hd : IsUnit (w.b + W.a₁ * w.a)) :
    nodeNegativeParameter v * nodePositiveParameter w = nodePositiveParameter u := by
  have hc := node_add_unit_tangent_character D v w u hk hkw hw hb hd
  have hα := (residue_ne_zero_iff_isUnit _).mpr D.a₁_unit
  have hbv := (residue_ne_zero_iff_isUnit _).mpr hb
  dsimp [nodePositiveParameter, nodeNegativeParameter]
  field_simp
  linear_combination -hc

end FLT.Mazur

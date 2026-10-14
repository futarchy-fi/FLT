/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeMiddleReductionCharacter
public import FLT.Mazur.EllipticNodeOppositeSmoothCharacter
public import FLT.Mazur.EllipticNodeMiddleSumLaurentCharacter

/-!
# The actual E₀ character of a middle-depth sum

Two midpoint witnesses determine the character of their actual sum, including
vertical and nonintegral sums. The two midpoint tangent factors also express
this as a symmetric product law with the normalized a₆ coefficient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
set_option backward.isDefEq.respectTransparency false
open IsLocalRing WeierstrassCurve
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  [DecidableEq (ResidueField A)]
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- Midpoint inputs compute the original smooth character of their actual sum. -/
theorem node_middle_smooth_character
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 2 * v.depth = n) (hw : 2 * w.depth = n) :
    residue A v.b * (Additive.toMul (splitDepthSmoothCharacter D
      ⟨P + Q, v.smooth_add_of_middle D w hv hw⟩)).val =
      -residue A (w.b + W.a₁ * w.a) := by
  classical
  have hn := D.depth_pos
  have he : v.depth = w.depth := by omega
  have hs := v.smooth_add_of_middle D w hv hw
  have hq := node_sum_reducesTo_smoothReduction v w hs
  have hc := node_middle_reduction_character D v.depth (by omega) (by omega)
    v.a v.b w.a w.b v.nonsingular (by simpa only [he] using w.nonsingular)
    (v.units_of_middle D hv).1 (w.units_of_middle D hw).2
    ((Projective.Point.toAffineAddEquiv (W.map (residue A)).toProjective)
      (smoothReductionHom A W ⟨P + Q, hs⟩)) (by simpa only [he] using hq)
  exact hc

/-- The midpoint product law uses the original normalized coefficient, without choosing roots. -/
theorem node_middle_smooth_product_character
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 2 * v.depth = n) (hw : 2 * w.depth = n)
    (c₆ : A) (h6 : W.a₆ = π ^ n * c₆) :
    residue A v.b * residue A w.b * (Additive.toMul (splitDepthSmoothCharacter D
      ⟨P + Q, v.smooth_add_of_middle D w hv hw⟩)).val = -residue A c₆ := by
  have hc := node_middle_smooth_character D v w hv hw
  have ht := node_middle_tangent_character D w hw c₆ h6
  linear_combination residue A w.b * hc - ht

include D in
omit [DecidableEq (ResidueField A)] in
/-- The midpoint character law detects precisely when the actual sum enters E₁. -/
theorem node_middle_sum_infinity_iff
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 2 * v.depth = n) (hw : 2 * w.depth = n) :
    InfinityReduction A W (P + Q) ↔
      residue A v.b = -residue A (w.b + W.a₁ * w.a) := by
  classical
  let r : ellipticE0 A W := ⟨P + Q, v.smooth_add_of_middle D w hv hw⟩
  have hc := node_middle_smooth_character D v w hv hw
  have hi : splitDepthSmoothCharacter D r = 0 ↔ InfinityReduction A W (P + Q) := by
    rw [← map_zero (splitDepthSmoothCharacter D), splitDepthSmoothCharacter_eq_iff,
      map_zero]
    exact smoothReductionPoint_eq_zero_iff A W r
  rw [← hi]
  constructor
  · intro hz
    change residue A v.b * (Additive.toMul (splitDepthSmoothCharacter D r)).val = _ at hc
    rw [hz] at hc
    simpa using hc
  · intro heq
    have hu : (Additive.toMul (splitDepthSmoothCharacter D r)).val = 1 := by
      apply mul_left_cancel₀ ((residue_ne_zero_iff_isUnit _).mpr (v.units_of_middle D hv).1)
      simpa only [mul_one, heq] using hc
    exact congrArg Additive.ofMul (Units.ext hu)

end FLT.Mazur

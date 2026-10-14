/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeOppositeReductionCharacter
public import FLT.Mazur.EllipticNodeOppositeLabels

/-!
# The character of actual equal-depth sums in E₀

Primitive witnesses on opposite strict branches determine the multiplicative
character of the actual sum in E₀. The formula includes sums equal to zero
and nonintegral sums, and therefore does not require an affine output witness.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
set_option backward.isDefEq.respectTransparency false
open IsLocalRing WeierstrassCurve
variable {K : Type*} [Field K] [DecidableEq K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  [DecidableEq (ResidueField A)]
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

/-- The original affine sum reduces to the affine form of its actual smooth reduction. -/
theorem node_sum_reducesTo_smoothReduction
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hs : SmoothReduction A W (P + Q)) :
    ReducesTo A W (Affine.Point.some _ _ v.nonsingular + .some _ _ w.nonsingular)
      ((Projective.Point.toAffineAddEquiv (W.map (residue A)).toProjective)
        (smoothReductionHom A W ⟨P + Q, hs⟩)) := by
  classical
  let e := Projective.Point.toAffineAddEquiv (W.map (residue A)).toProjective
  have he (R) : (e R).toProjective = R := e.symm_apply_apply R
  change projectiveReduction A W
    (Affine.Point.some _ _ v.nonsingular + .some _ _ w.nonsingular).toProjective =
      (e (smoothReductionHom A W ⟨P + Q, hs⟩)).toProjective.point
  rw [he, toProjective_add, ← v.represents, ← w.represents]
  rfl

omit [DecidableEq K] in
/-- Equal-depth opposite inputs compute the actual E₀ character of their sum. -/
theorem node_opposite_smooth_character
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hn : 2 * v.depth < n) (he : v.depth = w.depth)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    residue A w.b * (Additive.toMul (splitDepthSmoothCharacter D
      ⟨P + Q, v.smooth_add_of_opposite D w hk hn he hb hd⟩)).val =
      -residue A (v.b + W.a₁ * v.a) := by
  classical
  obtain ⟨ha, _⟩ := node_point_branches_below_middle W D.uniformizer_ne_zero
    D.maximalIdeal_eq n v.depth hk hn D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem
    v.a v.b v.primitive v.equation
  obtain ⟨_, ht⟩ := node_point_branches_below_middle W D.uniformizer_ne_zero
    D.maximalIdeal_eq n w.depth (by omega) (by omega)
    D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem w.a w.b w.primitive w.equation
  have hdt : w.b + W.a₁ * w.a ∈ maximalIdeal A := by
    rcases ht with h | h
    · exact (h.1 hd).elim
    · exact h.2
  have hs := v.smooth_add_of_opposite D w hk hn he hb hd
  have hq := node_sum_reducesTo_smoothReduction v w hs
  have hc := node_opposite_reduction_character D v.depth hk v.a v.b w.a w.b
    v.nonsingular (by simpa only [he] using w.nonsingular) ha hb hd hdt
    ((Projective.Point.toAffineAddEquiv (W.map (residue A)).toProjective)
      (smoothReductionHom A W ⟨P + Q, hs⟩)) (by simpa only [he] using hq)
  exact hc

include D in
omit [DecidableEq K] [DecidableEq (ResidueField A)] in
/-- The opposite-character quotient equals one precisely when the actual sum enters E₁. -/
theorem node_opposite_sum_infinity_iff
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hn : 2 * v.depth < n) (he : v.depth = w.depth)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    InfinityReduction A W (P + Q) ↔
      residue A w.b = -residue A (v.b + W.a₁ * v.a) := by
  classical
  let r : ellipticE0 A W := ⟨P + Q, v.smooth_add_of_opposite D w hk hn he hb hd⟩
  have hc := node_opposite_smooth_character D v w hk hn he hb hd
  have hi : splitDepthSmoothCharacter D r = 0 ↔ InfinityReduction A W (P + Q) := by
    rw [← map_zero (splitDepthSmoothCharacter D), splitDepthSmoothCharacter_eq_iff,
      map_zero]
    exact smoothReductionPoint_eq_zero_iff A W r
  rw [← hi]
  constructor
  · intro hz
    change residue A w.b * (Additive.toMul (splitDepthSmoothCharacter D r)).val = _ at hc
    rw [hz] at hc
    simpa using hc
  · intro heq
    have hu : (Additive.toMul (splitDepthSmoothCharacter D r)).val = 1 := by
      apply mul_left_cancel₀ ((residue_ne_zero_iff_isUnit _).mpr hd)
      simpa only [mul_one, heq] using hc
    exact congrArg Additive.ofMul (Units.ext hu)

end FLT.Mazur

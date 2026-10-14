/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedComponentCharacterEquality
public import FLT.Mazur.EllipticNodeOppositeSmoothCharacter

/-!
# Equal-depth opposite translation in the actual resolved fiber

Translation from a strict positive component into E₀ preserves and reflects
equality of original smooth specializations. The result includes the final
odd-depth component, vertical sums, and sums with nonintegral coordinates.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open IsLocalRing
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P P' Q : (W.map (algebraMap A K)).toProjective.Point}

/-- Equal-depth opposite translation detects exactly the original resolved smooth-fiber equality. -/
theorem resolvedSplitSmoothPoint_opposite_translation_eq_iff
    (v : NodePointCoordinates A W π P) (v' : NodePointCoordinates A W π P')
    (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hn : 2 * v.depth < n)
    (he : v'.depth = v.depth) (hw : w.depth = v.depth)
    (hb : v.b ∈ maximalIdeal A) (hb' : v'.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    resolvedSplitSmoothPoint A D (P + Q) = resolvedSplitSmoothPoint A D (P' + Q) ↔
      resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D P' := by
  classical
  let r : ellipticE0 A W := ⟨P + Q, v.smooth_add_of_opposite D w hk hn hw.symm hb hd⟩
  let r' : ellipticE0 A W := ⟨P' + Q,
    v'.smooth_add_of_opposite D w (by omega) (by omega) (by omega) hb' hd⟩
  change resolvedSplitSmoothPoint A D r.val = resolvedSplitSmoothPoint A D r'.val ↔ _
  rw [resolvedSplitSmoothPoint_e0_character_eq_iff,
    resolvedSplitSmoothPoint_strict_positive_eq_iff A D v.depth hk hn P P' v rfl v' he hb hb']
  have hc := node_opposite_smooth_character D v w hk hn hw.symm hb hd
  have hc' := node_opposite_smooth_character D v' w (by omega) (by omega) (by omega) hb' hd
  change residue A w.b * (Additive.toMul (splitDepthSmoothCharacter D r)).val = _ at hc
  change residue A w.b * (Additive.toMul (splitDepthSmoothCharacter D r')).val = _ at hc'
  constructor
  · intro h
    have hu := congrArg (fun z : Additive (ResidueField A)ˣ => z.toMul.val) h
    apply neg_injective
    rw [← hc, ← hc', hu]
  · intro h
    apply Additive.toMul.injective
    apply Units.ext
    apply mul_left_cancel₀ ((residue_ne_zero_iff_isUnit _).mpr hd)
    rw [hc, hc', h]

/-- Equal-depth opposite translation preserves and detects equality to the actual identity. -/
theorem resolvedSplitSmoothPoint_opposite_sum_eq_zero_iff
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hk : 0 < v.depth) (hn : 2 * v.depth < n) (he : v.depth = w.depth)
    (hb : v.b ∈ maximalIdeal A) (hd : IsUnit w.b) :
    resolvedSplitSmoothPoint A D (P + Q) = resolvedSplitSmoothPoint A D 0 ↔
      residue A w.b = -residue A (v.b + W.a₁ * v.a) := by
  classical
  let r : ellipticE0 A W := ⟨P + Q, v.smooth_add_of_opposite D w hk hn he hb hd⟩
  change resolvedSplitSmoothPoint A D r.val =
    resolvedSplitSmoothPoint A D (0 : ellipticE0 A W).val ↔ _
  rw [resolvedSplitSmoothPoint_e0_character_eq_iff, map_zero,
    ← map_zero (splitDepthSmoothCharacter D), splitDepthSmoothCharacter_eq_iff, map_zero]
  exact (smoothReductionPoint_eq_zero_iff A W r).trans
    (node_opposite_sum_infinity_iff D v w hk hn he hb hd)

end FLT.Mazur.WeierstrassDividedDepth

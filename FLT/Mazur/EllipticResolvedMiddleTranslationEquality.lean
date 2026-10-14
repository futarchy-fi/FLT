/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedComponentCharacterEquality
public import FLT.Mazur.EllipticNodeMiddleSmoothCharacter

/-!
# Midpoint translation in the actual resolved smooth fiber

Translation by a midpoint point takes the midpoint component to E₀ and
preserves and reflects equality of actual proper specializations. The proof
uses original characters and includes every exceptional slope chart.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open IsLocalRing
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P P' Q : (W.map (algebraMap A K)).toProjective.Point}

/-- Midpoint translation detects exactly the original resolved smooth-fiber equality. -/
theorem resolvedSplitSmoothPoint_middle_translation_eq_iff
    (v : NodePointCoordinates A W π P) (v' : NodePointCoordinates A W π P')
    (w : NodePointCoordinates A W π Q)
    (hv : 2 * v.depth = n) (hv' : 2 * v'.depth = n) (hw : 2 * w.depth = n) :
    resolvedSplitSmoothPoint A D (P + Q) = resolvedSplitSmoothPoint A D (P' + Q) ↔
      resolvedSplitSmoothPoint A D P = resolvedSplitSmoothPoint A D P' := by
  classical
  let r : ellipticE0 A W := ⟨P + Q, v.smooth_add_of_middle D w hv hw⟩
  let r' : ellipticE0 A W := ⟨P' + Q, v'.smooth_add_of_middle D w hv' hw⟩
  change resolvedSplitSmoothPoint A D r.val = resolvedSplitSmoothPoint A D r'.val ↔ _
  rw [resolvedSplitSmoothPoint_e0_character_eq_iff,
    resolvedSplitSmoothPoint_middle_character_eq_iff A D P P' v v' hv hv']
  have hc := node_middle_smooth_character D v w hv hw
  have hc' := node_middle_smooth_character D v' w hv' hw
  change residue A v.b * (Additive.toMul (splitDepthSmoothCharacter D r)).val = _ at hc
  change residue A v'.b * (Additive.toMul (splitDepthSmoothCharacter D r')).val = _ at hc'
  constructor
  · intro h
    have hu := congrArg (fun z : Additive (ResidueField A)ˣ => z.toMul.val) h
    apply mul_right_cancel₀ (Additive.toMul (splitDepthSmoothCharacter D r')).ne_zero
    rw [← hu, hc, hu, hc']
  · intro h
    apply Additive.toMul.injective
    apply Units.ext
    apply mul_left_cancel₀ ((residue_ne_zero_iff_isUnit _).mpr (v.units_of_middle D hv).1)
    rw [hc, h, hc']

/-- A midpoint sum specializes to the identity precisely at the predicted tangent residue. -/
theorem resolvedSplitSmoothPoint_middle_sum_eq_zero_iff
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (hv : 2 * v.depth = n) (hw : 2 * w.depth = n) :
    resolvedSplitSmoothPoint A D (P + Q) = resolvedSplitSmoothPoint A D 0 ↔
      residue A v.b = -residue A (w.b + W.a₁ * w.a) := by
  classical
  let r : ellipticE0 A W := ⟨P + Q, v.smooth_add_of_middle D w hv hw⟩
  change resolvedSplitSmoothPoint A D r.val =
    resolvedSplitSmoothPoint A D (0 : ellipticE0 A W).val ↔ _
  rw [resolvedSplitSmoothPoint_e0_character_eq_iff, map_zero,
    ← map_zero (splitDepthSmoothCharacter D), splitDepthSmoothCharacter_eq_iff, map_zero]
  exact (smoothReductionPoint_eq_zero_iff A W r).trans
    (node_middle_sum_infinity_iff D v w hv hw)

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasBaseChangeCover

/-!
# Common refinements of base-change chart pairs

Original source and target charts refine simultaneously around every source
point. The geometric maps of their bases satisfy the original refinement square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasBaseChangeCharts
open FCurve AffineFiniteFreeAtlas
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (hM : LocallyFiniteFree M)

include hM in
/-- Chart pairs have simultaneous source and target refinements on every overlap. -/
lemma common_refinement (c d : Chart f M) {x : X}
    (hc : x ∈ c.source.val) (hd : x ∈ d.source.val) :
    ∃ e : Chart f M, x ∈ e.source.val ∧ e.source ≤ c.source ∧
      e.source ≤ d.source ∧ e.target ≤ c.target ∧ e.target ≤ d.target := by
  obtain ⟨j, hj, hjc, hjd⟩ := AffineFiniteFreeAtlas.common_refinement M hM c.target d.target
    (c.le_preimage hc) (d.le_preimage hd)
  obtain ⟨i, hi, hle⟩ := exists_mem_le ((pullback f).obj M) (hM.pullback f)
    (show x ∈ (c.source.val ⊓ d.source.val) ⊓ f ⁻¹ᵁ j.val from ⟨⟨hc, hd⟩, hj⟩)
  exact ⟨⟨i, j, hle.trans inf_le_right⟩, hi,
    hle.trans (inf_le_left.trans inf_le_left),
    hle.trans (inf_le_left.trans inf_le_right), hjc, hjd⟩

/-- The maps between original affine bases commute with simultaneous refinements. -/
@[reassoc]
lemma baseMap_refinement (c d : Chart f M)
    (hi : c.source ≤ d.source) (hj : c.target ≤ d.target) :
    X.homOfLE hi ≫ baseMap f M d.source d.target d.le_preimage =
      baseMap f M c.source c.target c.le_preimage ≫ Y.homOfLE hj := by
  apply (cancel_mono d.target.val.ι).mp
  simp only [Category.assoc, baseMap_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc]

end FLT.Mazur.DualAtlasBaseChangeCharts

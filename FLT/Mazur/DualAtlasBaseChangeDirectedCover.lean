/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasBaseChangeRefinement
public import FLT.Mazur.DualAtlasChartRefinement

/-!
# Directed original projective charts for base change

Simultaneous refinement orders the original source and target chart pairs.
The original projective chart cover is locally directed in this order, so
compatible scheme morphisms on these charts descend to the actual atlas.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits hiding pullback
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasBaseChangeCharts
open FCurve AffineFiniteFreeAtlas FiniteFreeChartTransitions ProjectiveSpace
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (hM : LocallyFiniteFree M)

/-- Simultaneous containment in the original source and target affine charts. -/
instance : PartialOrder (Chart f M) where
  le c d := c.source ≤ d.source ∧ c.target ≤ d.target
  le_refl c := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h k := ⟨h.1.trans k.1, h.2.trans k.2⟩
  le_antisymm c d h k := by
    have hs := le_antisymm h.1 k.1
    have ht := le_antisymm h.2 k.2
    cases c; cases d
    dsimp at hs ht
    cases hs; cases ht
    rfl

instance : PartialOrder (projectiveCover f M hM).I₀ :=
  inferInstanceAs (PartialOrder (Chart f M))

/-- The supported original projective charts have simultaneous refinements on overlaps. -/
instance projectiveCoverLocallyDirected : (projectiveCover f M hM).LocallyDirected where
  trans {c d} h := dualChartInclusion ((pullback f).obj M) h.le.1
    (chart ((pullback f).obj M) c.source) (chart ((pullback f).obj M) d.source)
  trans_id c := dualChartInclusion_self _ _
  trans_comp h k := (dualChartInclusion_comp _ h.le.1 k.le.1 _ _ _).symm
  w h := LocallyFreeDualProjectiveAtlas.chart_refinement _ _ h.le.1
  directed {c d} x := by
    let a := (projectiveCover f M hM).f c
    let b := (projectiveCover f M hM).f d
    let xi := Limits.pullback.fst a b x
    let xj := Limits.pullback.snd a b x
    have he : a xi = b xj := by
      simpa only [xi, xj, ← Scheme.Hom.comp_apply] using
        congrArg (fun k : Limits.pullback a b ⟶ _ ↦ k x)
          (Limits.pullback.condition (f := a) (g := b))
    let p := LocallyFreeDualProjectiveAtlas.projection ((pullback f).obj M) (hM.pullback f)
    have hc : p (a xi) ∈ c.source.val := by
      change (LocallyFreeDualProjectiveAtlas.chartMap _ _ c.source ≫
        LocallyFreeDualProjectiveAtlas.projection _ _) xi ∈ c.source.val
      rw [LocallyFreeDualProjectiveAtlas.chart_projection]
      exact (affineProjection c.source.val.toScheme _ xi).property
    have hd : p (a xi) ∈ d.source.val := by
      rw [he]
      change (LocallyFreeDualProjectiveAtlas.chartMap _ _ d.source ≫
        LocallyFreeDualProjectiveAtlas.projection _ _) xj ∈ d.source.val
      rw [LocallyFreeDualProjectiveAtlas.chart_projection]
      exact (affineProjection d.source.val.toScheme _ xj).property
    obtain ⟨e, hx, hec, hed, htc, htd⟩ := common_refinement f M hM c d hc hd
    obtain ⟨y, hy⟩ := LocallyFreeDualProjectiveAtlas.exists_chart_preimage
      ((pullback f).obj M) (hM.pullback f) e.source (a xi) hx
    refine ⟨e, homOfLE ⟨hec, htc⟩, homOfLE ⟨hed, htd⟩, y, ?_⟩
    apply (Limits.pullback.fst a b).injective
    apply a.injective
    change (Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst a b ≫ a) y = a xi
    rw [Limits.pullback.lift_fst_assoc]
    change (dualChartInclusion _ hec _ _ ≫
      LocallyFreeDualProjectiveAtlas.chartMap _ _ c.source) y = a xi
    rw [LocallyFreeDualProjectiveAtlas.chart_refinement]
    exact hy

end FLT.Mazur.DualAtlasBaseChangeCharts

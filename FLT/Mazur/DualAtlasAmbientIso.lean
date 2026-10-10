/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasAmbientMap

/-!
# The global atlas isomorphism for an ambient sheaf isomorphism

The original chart maps respect identities and composition. Consequently the
independently descended global maps are inverse scheme isomorphisms over the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasAmbient
open FCurve AffineFiniteFreeAtlas DualFreeSheafCoordinates
variable {X : Scheme.{u}} {M N P : X.Modules}

/-- Identity ambient transport is the identity on every original chart. -/
lemma chartIso_refl (i : Index M) : chartIso (Iso.refl M) i = Iso.refl _ := by
  have h : change (Iso.refl M) i = Iso.refl _ := by
    apply Iso.ext
    change (chart M i).inv ≫ (restrictFunctor i.val.ι).map (𝟙 M) ≫
      (chart M i).hom = 𝟙 _
    simp
  rw [chartIso, h, projectiveIso_refl]

/-- Ambient composition is computed by composition of the actual chosen coordinate maps. -/
lemma chartIso_trans (a : M ≅ N) (b : N ≅ P) (i : Index M) :
    chartIso (a ≪≫ b) i = chartIso a i ≪≫ chartIso b (index a i) := by
  have h : change (a ≪≫ b) i = change a i ≪≫ change b (index a i) := by
    apply Iso.ext
    simp only [change, FiniteFreeChartTransitions.ambientChange, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_assoc]
    rfl
  rw [chartIso, h, projectiveIso_trans]
  rfl

/-- The independently descended ambient map preserves the identity. -/
lemma map_refl (hM : LocallyFiniteFree M) : map (Iso.refl M) hM hM = 𝟙 _ := by
  apply (LocallyFreeDualProjectiveAtlas.cover M hM).hom_ext
  intro i
  change LocallyFreeDualProjectiveAtlas.chartMap M hM i ≫ _ =
    LocallyFreeDualProjectiveAtlas.chartMap M hM i ≫ _
  rw [chart_map, toAtlas, chartIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]
  rfl

/-- The actual global atlas maps compose in the order of the ambient sheaf isomorphisms. -/
@[reassoc]
lemma map_trans (a : M ≅ N) (b : N ≅ P)
    (hM : LocallyFiniteFree M) (hN : LocallyFiniteFree N) (hP : LocallyFiniteFree P) :
    map a hM hN ≫ map b hN hP = map (a ≪≫ b) hM hP := by
  apply (LocallyFreeDualProjectiveAtlas.cover M hM).hom_ext
  intro i
  change LocallyFreeDualProjectiveAtlas.chartMap M hM i ≫ _ =
    LocallyFreeDualProjectiveAtlas.chartMap M hM i ≫ _
  rw [chart_map_assoc, chart_map, toAtlas, Category.assoc, chart_map,
    toAtlas, toAtlas, chartIso_trans, Iso.trans_hom, Category.assoc]
  rfl

/-- Ambient sheaf isomorphisms induce actual global scheme isomorphisms of the atlases. -/
def iso (a : M ≅ N) (hM : LocallyFiniteFree M) (hN : LocallyFiniteFree N) :
    LocallyFreeDualProjectiveAtlas.space M hM ≅ LocallyFreeDualProjectiveAtlas.space N hN where
  hom := map a hM hN
  inv := map a.symm hN hM
  hom_inv_id := by rw [map_trans, Iso.self_symm_id, map_refl]
  inv_hom_id := by rw [map_trans, Iso.symm_self_id, map_refl]

/-- The actual atlas isomorphism preserves the original base projection. -/
@[reassoc]
lemma iso_projection (a : M ≅ N) (hM : LocallyFiniteFree M) (hN : LocallyFiniteFree N) :
    (iso a hM hN).hom ≫ LocallyFreeDualProjectiveAtlas.projection N hN =
      LocallyFreeDualProjectiveAtlas.projection M hM := map_projection a hM hN

end FLT.Mazur.DualAtlasAmbient

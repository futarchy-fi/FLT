/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNormalizationDominant
public import FLT.Mazur.OneGonProductEndpoints
public import FLT.Mazur.OneGonProductTorus
/-!
# Global descent on the base-changed one-gon

Normalization maps identifying the actual endpoint sections descend uniquely
on the full pulled-back one-gon, including its separate torus chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.OneGonProductDescent
open OneGonProductNormalization OneGonProductEndpoints PolygonProductAtlas
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem exists_desc {Y : Scheme.{u}} (h : ProjectiveLineProductCharts.product K S ⟶ Y)
    (w : endpoint K S false ≫ h = endpoint K S true ≫ h) :
    ∃! d : oneGonProduct K S ⟶ Y, normalizationProduct K S ≫ d = h := by
  classical
  let d := (node_desc K S h w).choose
  have hd : Spec.map (CommRingCat.ofHom (PolygonNodePresentation.B (R := S)).val.toRingHom) ≫ d =
      affineNormalizationLift K S ≫ h := (node_desc K S h w).choose_spec.1
  let u : ∀ b, oneGonChart K S b ⟶ Y := fun b ↦ match b with
    | false => d
    | true => OneGonProductTorus.torusNormalizationLift K S ≫ h
  apply SchematicDescentGluing.exists_desc_of_cover _ h (oneGonProductCover K S) u
  intro b
  cases b
  · apply (cancel_epi (node_isPullback K S).flip.isoPullback.hom).mp
    simp only [oneGonProductCover, Scheme.Cover.copy_f, Scheme.Cover.copy_X,
      IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
    exact hd.symm
  · apply (cancel_epi (OneGonProductTorus.torus_isPullback K S).flip.isoPullback.hom).mp
    simp only [oneGonProductCover, Scheme.Cover.copy_f, Scheme.Cover.copy_X,
      IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc, Category.id_comp]
    rfl

theorem desc_toBase {Y : Scheme.{u}} (h : ProjectiveLineProductCharts.product K S ⟶ Y)
    (b : Y ⟶ Spec (.of S)) (hb : h ≫ b = pullback.fst _ _) (d : oneGonProduct K S ⟶ Y)
    (hd : normalizationProduct K S ≫ d = h) : d ≫ b = pullback.fst _ _ := by
  apply (cancel_epi (normalizationProduct K S)).mp
  rw [← Category.assoc, hd, hb, normalizationProduct_fst]

theorem nodeSection_desc {Y : Scheme.{u}} (h : ProjectiveLineProductCharts.product K S ⟶ Y)
    (d : oneGonProduct K S ⟶ Y) (hd : normalizationProduct K S ≫ d = h) :
    nodeSection K S ≫ d = endpoint K S false ≫ h := by
  rw [← endpoint_normalization K S false, Category.assoc, hd]
end FLT.Mazur.OneGonProductDescent

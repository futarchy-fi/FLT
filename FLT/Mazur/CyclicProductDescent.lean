/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNormalizationDominant
public import FLT.Mazur.CyclicProductEndpoints
/-!
# Global descent on the base-changed cyclic polygon

An arbitrary-target map on the normalization with the endpoint relation
descends uniquely through the actual parameter pullback of the cyclic polygon.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.CyclicProductDescent
open CyclicProductNormalization CyclicProductEndpoints PolygonProductAtlas
variable (K S : Type u) [Field K] [CommRing S] [Algebra K S]
variable (n : ℕ) (hn : 2 ≤ n)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem exists_desc {Y : Scheme.{u}} (h : componentsProduct K S n ⟶ Y)
    (w : ∀ j, endpoint K S n j false ≫ h = endpoint K S n j true ≫ h) :
    ∃! d : cyclicProduct K S n hn ⟶ Y, normalizationProduct K S n hn ≫ d = h := by
  classical
  let u (j : Fin n) := (node_desc K S n hn h j (w j)).choose
  have hu (j : Fin n) : NodeNormalizationBaseChange.normalization S ≫ u j =
      affineNormalizationLift K S n hn j ≫ h :=
    (node_desc K S n hn h j (w j)).choose_spec.1
  apply SchematicDescentGluing.exists_desc_of_cover _ h (cyclicProductCover K S n hn) u
  intro j
  apply (cancel_epi (node_isPullback K S n hn j).flip.isoPullback.hom).mp
  simp only [cyclicProductCover, Scheme.Cover.copy_f, Scheme.Cover.copy_X,
    IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
  exact (hu j).symm

theorem desc_toBase {Y : Scheme.{u}} (h : componentsProduct K S n ⟶ Y) (b : Y ⟶ Spec (.of S))
    (hb : h ≫ b = pullback.fst _ _) (d : cyclicProduct K S n hn ⟶ Y)
    (hd : normalizationProduct K S n hn ≫ d = h) : d ≫ b = pullback.fst _ _ := by
  apply (cancel_epi (normalizationProduct K S n hn)).mp
  rw [← Category.assoc, hd, hb, normalizationProduct_fst]
end FLT.Mazur.CyclicProductDescent

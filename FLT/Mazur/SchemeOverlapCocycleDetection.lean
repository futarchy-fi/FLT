/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapCocyclePullback
public import FLT.Mazur.ModuleSheafOpenImmersionGluing

/-!
# Detecting cocycles after normalized pullback to an open cover

A normalized composition law detects the pulled-back equation. Jointly
surjective open charts then detect the original composition law.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.SchemeOverlapCocycleChart
open SchemeOverlapDiagonalChart SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {Y T T' : Scheme.{u}}

/-- A normalized local composition law detects the actual pullback equation. -/
lemma map_hom_comp_of_normalize (c1 c2 c3 : T ⟶ Y) (t : T' ⟶ T)
    (d1 d2 d3 : T' ⟶ Y) (w1 : t ≫ c1 = d1) (w2 : t ≫ c2 = d2)
    (w3 : t ≫ c3 = d3) (M : Y.Modules)
    (e12 : (pullback c1).obj M ≅ (pullback c2).obj M)
    (e23 : (pullback c2).obj M ≅ (pullback c3).obj M)
    (e13 : (pullback c1).obj M ≅ (pullback c3).obj M)
    (h : (normalize c1 c2 t d1 d2 w1 w2 M e12).hom ≫
      (normalize c2 c3 t d2 d3 w2 w3 M e23).hom =
        (normalize c1 c3 t d1 d3 w1 w3 M e13).hom) :
    (pullback t).map (e12.hom ≫ e23.hom) = (pullback t).map e13.hom := by
  dsimp only [SchemeOverlapDiagonalChart.normalize, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom] at h
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc] at h
  have hh := (cancel_epi ((comparison t c1 d1 w1).inv.app M)).mp h
  rw [← Category.assoc] at hh
  have hh' := (cancel_mono ((comparison t c3 d3 w3).hom.app M)).mp hh
  simpa only [Functor.map_comp] using hh'

/-- Normalized composition equations on an open cover imply the global law. -/
lemma hom_comp_of_normalized_cover {ι : Type v} (S : ι → Scheme.{u})
    (t : ∀ i, S i ⟶ T) [∀ i, IsOpenImmersion (t i)]
    (hc : ∀ x : T, ∃ i, x ∈ Set.range (t i))
    (c1 c2 c3 : T ⟶ Y) (M : Y.Modules)
    (e12 : (pullback c1).obj M ≅ (pullback c2).obj M)
    (e23 : (pullback c2).obj M ≅ (pullback c3).obj M)
    (e13 : (pullback c1).obj M ≅ (pullback c3).obj M)
    (h : ∀ i,
      (normalize c1 c2 (t i) (t i ≫ c1) (t i ≫ c2) rfl rfl M e12).hom ≫
        (normalize c2 c3 (t i) (t i ≫ c2) (t i ≫ c3) rfl rfl M e23).hom =
      (normalize c1 c3 (t i) (t i ≫ c1) (t i ≫ c3) rfl rfl M e13).hom) :
    e12.hom ≫ e23.hom = e13.hom := by
  apply ModuleSheafOpenImmersionGluing.hom_ext S t hc
  intro i
  exact map_hom_comp_of_normalize c1 c2 c3 (t i) _ _ _ rfl rfl rfl M
    e12 e23 e13 (h i)

end FLT.Mazur.SchemeOverlapCocycleChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackAmbientSectionMatch

/-!
# Refining ambient comparisons on arbitrary source schemes

The two ambient identifications on a test and its refinement agree with the
actual pullback path. Consequently every original global quotient projection
has compatible coordinate projections on those tests.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SheafPullbackAmbientTestRefinement
open SheafPullbackPathComparison SheafPullbackAmbientNormalization
universe u
variable {S T X Y : Scheme.{u}}
variable (l : T ⟶ Y) (i : Y ⟶ X) (β : X ⟶ S)
  (j : T ⟶ X) (s : Y ⟶ S) (t : T ⟶ S)
  (hli : l ≫ i = j) (hi : i ≫ β = s) (hj : j ≫ β = t) (hl : l ≫ s = t)
variable (L : S.Modules) {V : Y.Modules} {K : T.Modules}
  (a : (pullback s).obj L ≅ V) (e : (pullback l).obj V ≅ K)
  (c : (pullback t).obj L ≅ K)
attribute [local irreducible] Scheme.Modules.pullback comparison

/-- Coherence of the original coefficient ambient maps implies coherence on source tests. -/
theorem testIso_refinement
    (hc : SheafPullbackAmbientSectionMatch.Composes l s t hl L a e c) :
    (pullback l).map (testIso i β s hi L V a).hom ≫ e.hom =
      (comparison l i j hli).hom.app ((pullback β).obj L) ≫
        (testIso j β t hj L K c).hom := by
  have h := hc
  unfold SheafPullbackAmbientSectionMatch.Composes at h
  rw [SheafPullbackAmbientCoherence.compositeIso_eq] at h
  have he : (pullback l).map a.hom ≫ e.hom =
      (comparison l s t hl).hom.app L ≫ c.hom := by
    apply (cancel_epi ((comparison l s t hl).inv.app L)).mp
    simpa only [Category.assoc, Iso.app_inv, Iso.inv_hom_id_app_assoc] using h
  unfold testIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [he, comparison_assoc_assoc l i β j s t hli hi hl hj]

/-- The normalized quotient on a refined test is the pullback of its original projection. -/
theorem quotient_refinement
    (hc : SheafPullbackAmbientSectionMatch.Composes l s t hl L a e c)
    {P : X.Modules} (p : (pullback β).obj L ⟶ P) :
    e.inv ≫ (pullback l).map ((testIso i β s hi L V a).inv ≫ (pullback i).map p) =
      ((testIso j β t hj L K c).inv ≫ (pullback j).map p) ≫
        (comparison l i j hli).inv.app P := by
  apply SheafPullbackAmbientMatch.projection (pullback i) (pullback l) (pullback j)
    (comparison l i j hli) (testIso i β s hi L V a) e (testIso j β t hj L K c)
  unfold SheafPullbackAmbientMatch.Matches
  exact testIso_refinement l i β j s t hli hi hj hl L a e c hc

end FLT.Mazur.SheafPullbackAmbientTestRefinement

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackAmbientNormalization

/-!
# Original chart quotient maps from a common ambient pullback

The base comparison constructs each chart map. Path associativity identifies
its coordinate pullback with the full normalized quotient map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SheafPullbackAmbientNormalization
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {B W X Y : Scheme.{u}} (β : X ⟶ B) (i : Y ⟶ X) (s : Y ⟶ B)
  (hi : i ≫ β = s) (L : B.Modules) (V Q : Y.Modules)
  (a : (pullback s).obj L ≅ V) (q : V ⟶ Q)
attribute [local irreducible] Scheme.Modules.pullback comparison

/-- The original quotient map on a chart, normalized against the global ambient. -/
@[irreducible] def ambientChartMap : (pullback i).obj ((pullback β).obj L) ⟶ Q :=
  (comparison i β s hi).hom.app L ≫ a.hom ≫ q

variable (p : W ⟶ Y) (r : W ⟶ X) (t : W ⟶ B)
  (hr : p ≫ i = r) (ht : r ≫ β = t) (hp : p ≫ s = t)

/-- Every coordinate sees the same normalized full quotient from the base ambient. -/
theorem ambientChartMap_coordinate :
    (comparison p i r hr).inv.app ((pullback β).obj L) ≫
        (pullback p).map (ambientChartMap β i s hi L V Q a q) =
      (comparison r β t ht).hom.app L ≫ (chartIso p s t hp L V a).inv ≫
        (pullback p).map q := by
  unfold ambientChartMap chartIso
  simp only [Functor.map_comp, Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv,
    Iso.symm_inv, Category.assoc]
  apply (cancel_epi ((comparison p i r hr).hom.app ((pullback β).obj L))).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← comparison_assoc_assoc p i β r s t hr hi hp ht]
  simp only [Iso.hom_inv_id_app_assoc]

end FLT.Mazur.SheafPullbackAmbientNormalization

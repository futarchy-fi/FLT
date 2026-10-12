/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Normalizing ambient quotient maps on tests

A coherent ambient comparison identifies a pulled-back global quotient map
with its coordinate projection. All scheme paths and the full quotient map
are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SheafPullbackAmbientNormalization
open SheafPullbackPathComparison
universe u
variable {S T X Y : Scheme.{u}}
variable (z : T ⟶ X) (p : X ⟶ Y) (s : Y ⟶ S) (β : X ⟶ S)
  (g : T ⟶ Y) (t : T ⟶ S)
  (hp : p ≫ s = β) (hg : z ≫ p = g) (ht : z ≫ β = t) (hgt : g ≫ s = t)
variable (L : S.Modules) (V : Y.Modules) (K : T.Modules)
  (a : (pullback s).obj L ≅ V) (c : (pullback t).obj L ≅ K)
  (e : (pullback g).obj V ≅ K)
attribute [local irreducible] Scheme.Modules.pullback comparison

/-- The global chart ambient comparison from its original base module. -/
@[irreducible] def chartIso : (pullback p).obj V ≅ (pullback β).obj L :=
  (pullback p).mapIso a.symm ≪≫ (comparison p s β hp).app L

/-- The base ambient comparison on the test. -/
@[irreducible] def testIso : (pullback z).obj ((pullback β).obj L) ≅ K :=
  (comparison z β t ht).app L ≪≫ c

/-- Ambient coherence normalizes the entire chart comparison on the test. -/
theorem chartIso_test
    (hc : e.inv ≫ (pullback g).map a.inv ≫ (comparison g s t hgt).hom.app L = c.inv) :
    (pullback z).map (chartIso p s β hp L V a).hom ≫
      (testIso z β t ht L K c).hom = (comparison z p g hg).hom.app V ≫ e.hom := by
  have he : (pullback g).map a.inv ≫ (comparison g s t hgt).hom.app L ≫ c.hom =
      e.hom := by
    apply (cancel_epi e.inv).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun f ↦ f ≫ c.hom) hc
  unfold chartIso testIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  rw [comparison_assoc_assoc z p s g β t hg hp ht hgt]
  have hn := (comparison z p g hg).hom.naturality a.inv
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc ((pullback z).map ((pullback p).map a.inv)), hn]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ (comparison z p g hg).hom.app V ≫ f) he

/-- The normalized global quotient map becomes its full coordinate projection. -/
theorem quotientMap_test (Q : Y.Modules) (q : V ⟶ Q)
    (hc : e.inv ≫ (pullback g).map a.inv ≫ (comparison g s t hgt).hom.app L = c.inv) :
    (testIso z β t ht L K c).inv ≫
      (pullback z).map ((chartIso p s β hp L V a).inv ≫ (pullback p).map q) =
        e.inv ≫ (pullback g).map q ≫ (comparison z p g hg).inv.app Q := by
  apply (cancel_epi (testIso z β t ht L K c).hom).mp
  apply (cancel_epi ((pullback z).map (chartIso p s β hp L V a).hom)).mp
  simp only [Iso.hom_inv_id_assoc, Functor.map_comp,
    ← Functor.map_comp_assoc, Iso.hom_inv_id]
  rw [← Category.assoc, ← Category.assoc,
    chartIso_test z p s β g t hp hg ht hgt L V K a c e hc]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc ((comparison z p g hg).hom.app V),
    ← (comparison z p g hg).hom.naturality q]
  simp only [Functor.comp_map, Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    (pullback z).map_id, Category.id_comp]

end FLT.Mazur.SheafPullbackAmbientNormalization

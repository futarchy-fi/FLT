/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackAmbientMatch

/-!
# Geometric refinement of normalized ambient quotients

The same original chart quotient can be pulled back along any further scheme
map. Path associativity identifies its normalized ambient comparison and its
full projection without any affine or flatness hypothesis.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SheafPullbackAmbientNormalization
open SheafPullbackPathComparison SheafPullbackAmbientMatch
universe u
variable {S T X Y : Scheme.{u}}
variable (z : T ⟶ X) (p : X ⟶ Y) (s : Y ⟶ S) (β : X ⟶ S)
  (g : T ⟶ Y) (t : T ⟶ S)
  (hp : p ≫ s = β) (hg : z ≫ p = g) (ht : z ≫ β = t) (hgt : g ≫ s = t)
variable (L : S.Modules) (V : Y.Modules) (a : (pullback s).obj L ≅ V)
attribute [local irreducible] Scheme.Modules.pullback comparison

/-- Normalized chart ambients commute with arbitrary further geometric pullback. -/
theorem chartIso_refines :
    Matches (pullback p) (pullback z) (pullback g) (comparison z p g hg)
      (chartIso p s β hp L V a) ((comparison z β t ht).app L)
      (chartIso g s t hgt L V a) := by
  unfold Matches chartIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Functor.map_comp, Category.assoc]
  rw [comparison_assoc z p s g β t hg hp ht hgt]
  have hn := (comparison z p g hg).hom.naturality a.inv
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc]

/-- The entire original quotient projection commutes with geometric refinement. -/
theorem quotientMap_refines (Q : Y.Modules) (q : V ⟶ Q) :
    (pullback z).map ((chartIso p s β hp L V a).inv ≫ (pullback p).map q) ≫
        (comparison z p g hg).hom.app Q =
      (comparison z β t ht).hom.app L ≫
        (chartIso g s t hgt L V a).inv ≫ (pullback g).map q := by
  have h := projection (pullback p) (pullback z) (pullback g) (comparison z p g hg)
    (chartIso p s β hp L V a) ((comparison z β t ht).app L)
    (chartIso g s t hgt L V a)
    (chartIso_refines z p s β g t hp hg ht hgt L V a) q
  apply (cancel_epi ((comparison z β t ht).inv.app L)).mp
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app,
    Category.comp_id, Iso.app_inv] using
      congrArg (fun f ↦ f ≫ (comparison z p g hg).hom.app Q) h

end FLT.Mazur.SheafPullbackAmbientNormalization

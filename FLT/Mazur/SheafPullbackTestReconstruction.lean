/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackNamedSquare
public import FLT.Mazur.SheafPullbackMapNormalization

/-!
# Reconstruction on a scheme test of a covering chart

A covering-chart recovery normalized to its original source map agrees
with base-chart recovery followed by the original reconstruction. The
identity is a consequence of the square comparison and its naturality.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackSquare
open SheafPullbackPathComparison SheafPullbackMapNormalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y U V T : Scheme.{u}}
variable (p : Y ⟶ X) (q : V ⟶ U) (a : U ⟶ X) (b : V ⟶ Y)
variable (w : b ≫ p = q ≫ a)
variable (t : T ⟶ V) (d : T ⟶ Y) (f : T ⟶ U) (z : T ⟶ X)
variable (hd : t ≫ b = d) (hf : t ≫ q = f)
variable (hdp : d ≫ p = z) (hfa : f ≫ a = z)

/-- A test of covering recovery factors through the original base reconstruction. -/
lemma test_reconstruction {L : X.Modules} {A : U.Modules} {M : Y.Modules}
    (e : (pullback a).obj L ≅ A) (r : (pullback q).obj A ≅ (pullback b).obj M) :
    normalize t b b d d hd hd
        (((squareIso a b p q w).app L ≪≫ (pullback q).mapIso e ≪≫ r).hom) =
      (comparison d p z hdp).hom.app L ≫
        (comparison f a z hfa).inv.app L ≫ (pullback f).map e.hom ≫
        (comparison t q f hf).inv.app A ≫ (pullback t).map r.hom ≫
        (comparison t b d hd).hom.app M := by
  apply (cancel_epi ((comparison t b d hd).hom.app ((pullback p).obj L))).mp
  rw [normalize_comm]
  have hn := (comparison t q f hf).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← comparison_square_named_assoc a b p q w t d f z hd hf hdp hfa L]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc ((comparison t q f hf).hom.app ((pullback a).obj L)), ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

end FLT.Mazur.SchemePullbackSquare

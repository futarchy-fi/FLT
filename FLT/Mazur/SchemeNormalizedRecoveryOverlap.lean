/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePullbackOverlapNormalization

/-!
# Recognizing the overlap from normalized recovery

An equation between the two normalized recovery maps identifies a given
overlap with the canonical overlap transported through reconstruction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackOverlap
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z : Scheme.{u}} (p : Y ⟶ X) (l r : Z ⟶ Y) (k : Z ⟶ X)
variable (hl : l ≫ p = k) (hr : r ≫ p = k)
variable {A : X.Modules} {M : Y.Modules}

/-- Normalized recovery determines the original overlap isomorphism. -/
lemma eq_chartOverlap_of_normalized_recovery (e : (pullback p).obj A ≅ M)
    (d : (pullback l).obj M ≅ (pullback r).obj M)
    (h : (comparison l p k hl).inv.app A ≫ (pullback l).map e.hom ≫ d.hom =
      (comparison r p k hr).inv.app A ≫ (pullback r).map e.hom) :
    d = chartOverlap p l r k hl hr A e := by
  apply Iso.ext
  apply (cancel_epi ((pullback l).mapIso e).hom).mp
  apply (cancel_epi ((comparison l p k hl).inv.app A)).mp
  simpa only [chartOverlap, overlap,
    AffineIteratedPullbackSections.compositeIso_eq_comparison,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc] using h

end FLT.Mazur.SchemePullbackOverlap

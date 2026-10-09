/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeCanonicalOverlapLaws

/-!
# The diagonal law for canonical pullback overlaps

Normalize the canonical overlap along a common section of its projections.
Both resulting paths are the identity, so the normalized overlap is the identity.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemePullbackOverlap
open SchemeOverlapDiagonalChart SheafPullbackPathComparison SchemeModulePullbackUnits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z : Scheme.{u}}

/-- A canonical pullback overlap restricts to the identity on the diagonal. -/
lemma overlap_diagonal (p : Y ⟶ X) (l r : Z ⟶ Y) (k : Z ⟶ X)
    (hl : l ≫ p = k) (hr : r ≫ p = k) (d : Y ⟶ Z)
    (hdl : d ≫ l = 𝟙 Y) (hdr : d ≫ r = 𝟙 Y) (A : X.Modules) :
    DiagonalCompatible l r d hdl hdr ((pullback p).obj A) (overlap p l r k hl hr A) := by
  have hn := normalize_overlap_base p l r k hl hr d (𝟙 Y) (𝟙 Y) hdl hdr p
    (Category.id_comp p) (Category.id_comp p) A
  rw [overlap_self] at hn
  have hh := congrArg Iso.hom hn
  have he := congrArg
    (fun f ↦ (comparison d l (𝟙 Y) hdl).hom.app ((pullback p).obj A) ≫ f) hh
  simp only [SchemeOverlapDiagonalChart.normalize, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Iso.app_hom, Functor.mapIso_hom, Iso.refl_hom, Iso.hom_inv_id_app_assoc,
    Category.comp_id] at he
  unfold DiagonalCompatible
  simpa only [retractIso, comparison, Iso.trans_hom, Iso.app_hom,
    NatTrans.comp_app, Category.assoc] using
    congrArg (fun f ↦ f ≫ (pullbackId Y).hom.app ((pullback p).obj A)) he

end FLT.Mazur.SchemePullbackOverlap

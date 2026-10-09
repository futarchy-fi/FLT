/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineReconstructionRecognition
public import FLT.Mazur.SchemeCanonicalOverlapLaws
public import FLT.Mazur.SchemeDescentPairTransport
public import FLT.Mazur.SchemePullbackSquareIdentity

/-!
# Recognition retains transport between independent source maps

An original-overlap recognition equation determines transport on every test
scheme. The two maps into the source remain independent throughout.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
open SchemePullbackOverlap SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y T : Scheme.{u}} {p : Y ⟶ X} {M : Y.Modules} (D : Data p M)
variable (A : X.Modules) (e : (pullback p).obj A ≅ M)
variable (he : D.overlap = chartOverlap p (Limits.pullback.fst p p)
  (Limits.pullback.snd p p) (Limits.pullback.fst p p ≫ p)
  rfl Limits.pullback.condition.symm A e)

include he in
/-- Original overlap recognition determines transport on any pair of source maps. -/
lemma transport_chartOverlap (b c : T ⟶ Y) (k : T ⟶ X)
    (hb : b ≫ p = k) (hc : c ≫ p = k) :
    D.transport b c (hb.trans hc.symm) = chartOverlap p b c k hb hc A e := by
  let t := Limits.pullback.lift b c (hb.trans hc.symm)
  have ht : t ≫ (Limits.pullback.fst p p ≫ p) = k := by
    rw [← Category.assoc, Limits.pullback.lift_fst, hb]
  unfold transport
  rw [he, normalize_chartOverlap p _ _ _ rfl Limits.pullback.condition.symm
    t b c (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
    (hb.trans ht.symm) (hc.trans ht.symm)]
  unfold chartOverlap
  rw [overlap_base_eq p b c _ k (hb.trans ht.symm) (hc.trans ht.symm) hb hc A]

include he in
/-- Reconstruction around two squares intertwines their original descent transport. -/
@[reassoc]
lemma recognitionChart_transport {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (a : Spec R ⟶ X) (b c : Spec S ⟶ Y)
    (hb : Spec.map φ ≫ a = b ≫ p) (hc : Spec.map φ ≫ a = c ≫ p) :
    (recognitionChart p A e φ a b hb).hom ≫
        (D.transport b c (hb.symm.trans hc)).hom =
      (recognitionChart p A e φ a c hc).hom := by
  rw [D.transport_chartOverlap A e he b c (Spec.map φ ≫ a) hb.symm hc.symm]
  have h₁ := SchemePullbackSquare.squareIso_comparison p (Spec.map φ) a b hb
    (Spec.map φ ≫ a) rfl hb.symm A
  have h₂ := SchemePullbackSquare.squareIso_comparison p (Spec.map φ) a c hc
    (Spec.map φ ≫ a) rfl hc.symm A
  simp only [recognitionChart, chartOverlap, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  change _ ≫ (comparison b p _ hb.symm).hom.app A ≫
    (comparison c p _ hc.symm).inv.app A ≫ _ = _
  rw [← Category.assoc, h₁, ← h₂, Category.assoc, Iso.hom_inv_id_app_assoc]

end FLT.Mazur.SchemeGeometricDescent.Data

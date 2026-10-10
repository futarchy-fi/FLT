/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineRecognitionRefinement
public import FLT.Mazur.SchemeRecognitionTransport
public import FLT.Mazur.SchemeAffineCrossRefinementComparison

/-!
# Recognition on cross refinements

The original overlap equation makes recognition commute with the middle
comparison between two independent source maps, and hence with the full
effective comparison on the common affine base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
private lemma middle_square {B E : Type*} [Category B] [Category E]
    (F : B ⥤ E) {a b c : B} {x y : E} (l : a ⟶ b) (r : a ⟶ c) (m : b ⟶ c)
    (u : F.obj b ⟶ x) (v : F.obj c ⟶ y) (l' : F.obj a ⟶ x) (r' : F.obj a ⟶ y)
    (t : x ⟶ y) (hl : F.map l ≫ u = l') (hr : F.map r ≫ v = r')
    (hm : F.map m ≫ v = u ≫ t) (ht : l' ≫ t = r') :
    F.map (l ≫ m) ≫ v = F.map r ≫ v := by
  rw [Functor.map_comp, Category.assoc, hm, ← Category.assoc, hl, ht, hr]

private lemma outer_square {B : Type*} [Category B] {a b c d x y z : B}
    (l : a ⟶ c) (r : b ⟶ d) (u : a ≅ x) (v : b ≅ x)
    (l' : x ⟶ y) (r' : x ⟶ z) (cl : c ≅ y) (cr : d ≅ z) (m : y ≅ z)
    (hl : l ≫ cl.hom = u.hom ≫ l') (hr : r ≫ cr.hom = v.hom ≫ r')
    (hm : l' ≫ m.hom = r') :
    l ≫ (cl ≪≫ m ≪≫ cr.symm).hom = u.hom ≫ v.inv ≫ r := by
  apply (cancel_mono cr.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [← Category.assoc l, hl, Category.assoc, hm, hr, Iso.inv_hom_id_assoc]

variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' : Chart p} (ρ : C.CrossRefinement C')
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (A : X.Modules) (e : (pullback p).obj A ≅ M)
variable (he : D.overlap = SchemePullbackOverlap.chartOverlap p
  (Limits.pullback.fst p p) (Limits.pullback.snd p p) (Limits.pullback.fst p p ≫ p)
  rfl Limits.pullback.condition.symm A e)
variable [((pullback ρ.leftChart.base).obj A).IsQuasicoherent]
variable [((pullback ρ.leftChart.cover).obj M).IsQuasicoherent]
variable [((pullback ρ.rightChart.cover).obj M).IsQuasicoherent]

local instance : ((pullback ρ.rightChart.base).obj A).IsQuasicoherent :=
  inferInstanceAs (((pullback ρ.leftChart.base).obj A).IsQuasicoherent)

/-- Recognition intertwines the middle comparison with independent source maps. -/
@[reassoc]
lemma recognitionIso_middleComparison :
    (ρ.leftChart.recognitionIso D A e he).hom ≫ (ρ.middleComparison D).hom =
      (ρ.rightChart.recognitionIso D A e he).hom := by
  apply AffineQuasicoherentPullbackFaithful.reconstruction_unique ρ.rightChart.ringMap
    ρ.rightChart.faithfullyFlat (ρ.rightChart.reconstruction D)
  exact middle_square (pullback (Spec.map ρ.ringMap))
    (ρ.leftChart.recognitionIso D A e he).hom (ρ.rightChart.recognitionIso D A e he).hom
    (ρ.middleComparison D).hom (ρ.leftChart.reconstruction D).hom
    (ρ.rightChart.reconstruction D).hom _ _
    (D.transport ρ.leftChart.cover ρ.rightChart.cover ρ.covers_over).hom
    (ρ.leftChart.recognitionIso_reconstruction D A e he)
    (ρ.rightChart.recognitionIso_reconstruction D A e he)
    (ρ.middleComparison_reconstruction D)
    (D.recognitionChart_transport A e he ρ.ringMap ρ.leftChart.base
      ρ.leftChart.cover ρ.rightChart.cover ρ.leftChart.square ρ.rightChart.square)

variable [((pullback C.base).obj A).IsQuasicoherent]
variable [((pullback C'.base).obj A).IsQuasicoherent]
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
attribute [local irreducible] recognitionIso middleComparison Chart.comparison

/-- Cross-refinement recognition retains both original source maps. -/
@[reassoc]
lemma recognitionIso_effectiveComparison :
    (pullback (Spec.map ρ.leftBase)).map (C.recognitionIso D A e he).hom ≫
        (ρ.effectiveComparison D).hom =
      (SheafPullbackPathComparison.comparison (Spec.map ρ.leftBase) C.base
        ρ.leftChart.base ρ.leftRefinement.base_over).hom.app A ≫
      (SheafPullbackPathComparison.comparison (Spec.map ρ.rightBase) C'.base
        ρ.rightChart.base ρ.rightRefinement.base_over).inv.app A ≫
      (pullback (Spec.map ρ.rightBase)).map (C'.recognitionIso D A e he).hom := by
  exact outer_square _ _
    ((SheafPullbackPathComparison.comparison (Spec.map ρ.leftBase) C.base
      ρ.leftChart.base ρ.leftRefinement.base_over).app A)
    ((SheafPullbackPathComparison.comparison (Spec.map ρ.rightBase) C'.base
      ρ.rightChart.base ρ.rightRefinement.base_over).app A)
    (ρ.leftChart.recognitionIso D A e he).hom (ρ.rightChart.recognitionIso D A e he).hom
    (C.comparison ρ.leftChart D ρ.leftRefinement)
    (C'.comparison ρ.rightChart D ρ.rightRefinement) (ρ.middleComparison D)
    (C.recognitionIso_refinement ρ.leftChart ρ.leftRefinement A e D he)
    (C'.recognitionIso_refinement ρ.rightChart ρ.rightRefinement A e D he)
    (ρ.recognitionIso_middleComparison D A e he)

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineRecognitionCrossRefinement
public import FLT.Mazur.SchemeAffineCommonBaseTestComparison

/-!
# Recognition on affine tests of base overlaps

Normalize recognition into the common base coordinates. The constructed
common faithfully flat cover proves agreement with the actual scheme-test
comparison, without identifying the two maps to the covering scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
private lemma normalize_square {B : Type*} [Category B] {a b x y z : B}
    (u : a ≅ x) (v : b ≅ x) (l : a ⟶ y) (r : b ⟶ z) (t : y ⟶ z)
    (h : l ≫ t = u.hom ≫ v.inv ≫ r) :
    u.inv ≫ l ≫ t = v.inv ≫ r := by
  rw [h, Iso.inv_hom_id_assoc]

variable {X Y W : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (A : X.Modules) (e : (pullback p).obj A ≅ M)
variable (he : D.overlap = SchemePullbackOverlap.chartOverlap p
  (Limits.pullback.fst p p) (Limits.pullback.snd p p) (Limits.pullback.fst p p ≫ p)
  rfl Limits.pullback.condition.symm A e)
variable [((pullback C.base).obj A).IsQuasicoherent]
variable [((pullback C.cover).obj M).IsQuasicoherent]

/-- Candidate recognition normalized on a common scheme test. -/
def recognitionTestIso (a : W ⟶ X) (b : W ⟶ Spec C.baseRing) (hb : b ≫ C.base = a) :
    (pullback a).obj A ≅ (pullback b).obj (C.sheaf D) :=
  (SheafPullbackPathComparison.comparison b C.base a hb).symm.app A ≪≫
    (pullback b).mapIso (C.recognitionIso D A e he)

variable [((pullback C'.base).obj A).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
attribute [local irreducible] recognitionIso CrossRefinement.effectiveComparison sheaf
  recognitionTestIso schemeTestComparison

/-- Recognition agrees with the scheme-test comparison in specified ring coordinates. -/
@[reassoc]
lemma recognitionTestIso_commonBase {R : CommRingCat.{u}}
    (f : C.baseRing ⟶ R) (g : C'.baseRing ⟶ R) (a : Spec R ⟶ X)
    (hf : Spec.map f ≫ C.base = a) (hg : Spec.map g ≫ C'.base = a) :
    (C.recognitionTestIso D A e he a (Spec.map f) hf).hom ≫
        C.schemeTestComparison C' D (Spec.map f) (Spec.map g) (hf.trans hg.symm) =
      (C'.recognitionTestIso D A e he a (Spec.map g) hg).hom := by
  subst a
  let ρ := C.commonBaseCrossRefinement C' f g hg.symm
  let _ : ((pullback ρ.leftChart.base).obj A).IsQuasicoherent :=
    SchemeGeometricDescent.Data.isQuasicoherent_compositeChartPullback f C.base
  rw [schemeTestComparison_commonBase]
  simp only [recognitionTestIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  exact normalize_square
    ((SheafPullbackPathComparison.comparison (Spec.map f) C.base
      (Spec.map f ≫ C.base) rfl).app A)
    ((SheafPullbackPathComparison.comparison (Spec.map g) C'.base
      (Spec.map f ≫ C.base) hg).app A) _ _ _
    (ρ.recognitionIso_effectiveComparison D A e he)

/-- Recognition on any affine test intertwines the two actual chart comparisons. -/
@[reassoc]
lemma recognitionTestIso_affine {R : CommRingCat.{u}}
    (a : Spec R ⟶ X) (b : Spec R ⟶ Spec C.baseRing) (c : Spec R ⟶ Spec C'.baseRing)
    (hb : b ≫ C.base = a) (hc : c ≫ C'.base = a) :
    (C.recognitionTestIso D A e he a b hb).hom ≫
        C.schemeTestComparison C' D b c (hb.trans hc.symm) =
      (C'.recognitionTestIso D A e he a c hc).hom := by
  obtain ⟨f, rfl⟩ : ∃ f : C.baseRing ⟶ R, Spec.map f = b :=
    ⟨Spec.preimage b, Spec.map_preimage b⟩
  obtain ⟨g, rfl⟩ : ∃ g : C'.baseRing ⟶ R, Spec.map g = c :=
    ⟨Spec.preimage c, Spec.map_preimage c⟩
  exact C.recognitionTestIso_commonBase C' D A e he f g a hb hc

end FLT.Mazur.SchemeAffineDescent.Chart

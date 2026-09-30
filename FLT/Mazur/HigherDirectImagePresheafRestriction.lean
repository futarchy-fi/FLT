/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HigherDirectImagePresheaf

/-!
# Restriction maps in the higher direct-image presheaf

The section-cocycle presentation identifies the existing homology presheaf
restriction with restriction of open Ext cohomology, in every degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

universe u

namespace FLT.Mazur.HigherDirectImagePresheaf

open OpenDirectImageCohomology OpenDirectImageNaturality

local instance restrictionSheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) := HasExt.standard _

local instance restrictionTopSheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} T) := HasExt.standard _

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The existing restriction of the section short complex. -/
def sectionComplexRestrict {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) {V U : Opens Y} (i : V ⟶ U) (n : ℕ) :
    sectionComplex f I U n ⟶ sectionComplex f I V n :=
  ((resolutionPresheaf f I).sc' (n - 1) n (n + 1)).mapNatTrans
    ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).map i.op)

/-- Evaluation of homology is natural for restriction of opens. -/
@[reassoc]
lemma evaluationIso_restrict {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) {V U : Opens Y} (i : V ⟶ U) (n : ℕ) :
    ShortComplex.homologyMap (sectionComplexRestrict f I i n) ≫
        (evaluationIso f I V n).hom =
      (evaluationIso f I U n).hom ≫ (presheaf f I n).map i.op := by
  let E := evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}
  have hi : (ComplexShape.up ℕ).prev n = n - 1 := by
    cases n <;> simp [CochainComplex.prev_nat_zero, CochainComplex.prev_nat_succ]
  let e := ((resolutionPresheaf f I).isoSc' (n - 1) n (n + 1) hi
    (CochainComplex.next ℕ n)).symm.hom
  have h : ((resolutionPresheaf f I).sc' (n - 1) n (n + 1)).mapNatTrans (E.map i.op) ≫
      (E.obj (op V)).mapShortComplex.map e =
    (E.obj (op U)).mapShortComplex.map e ≫
      ((resolutionPresheaf f I).sc n).mapNatTrans (E.map i.op) := by
    ext1
    · exact e.τ₁.naturality i.op
    · exact e.τ₂.naturality i.op
    · exact e.τ₃.naturality i.op
  have hh := congrArg (fun a ↦ ShortComplex.homologyMap a) h
  simp only [ShortComplex.homologyMap_comp] at hh
  dsimp only [evaluationIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [ShortComplex.homologyFunctor_map, Category.assoc]
  erw [← Category.assoc, hh, Category.assoc]
  rw [ShortComplex.homologyMap_mapNatTrans]
  dsimp only [E]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Homology restriction preserves the represented section cocycle. -/
lemma homologyClass_restrict {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) {V U : Opens Y} (i : V ⟶ U) (n : ℕ)
    (x : sectionCycles ((Opens.map f).obj U) I n) :
    (presheaf f I n).map i.op (homologyClass f I U n x) =
      homologyClass f I V n (sectionCyclesRestrict I ((Opens.map f).map i) n x) := by
  have h := ConcreteCategory.congr_hom (evaluationIso_restrict f I i n)
    ((sectionComplex f I U n).abHomologyIso.inv (QuotientAddGroup.mk' _ x))
  change (evaluationIso f I V n).hom _ =
    (presheaf f I n).map i.op (homologyClass f I U n x) at h
  erw [← h, homologyMap_cycle (sectionComplexRestrict f I i n) x
    (sectionCyclesRestrict I ((Opens.map f).map i) n x) rfl]
  rfl

/-- The pointwise comparison commutes with the original open restriction maps. -/
lemma openEquiv_restrict {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) {V U : Opens Y} (i : V ⟶ U) (n : ℕ)
    (x : (presheaf f I n).obj (op U)) :
    openEquiv f I V n ((presheaf f I n).map i.op x) =
      (F.cohomologyPresheaf n).map ((Opens.map f).map i).op (openEquiv f I U n x) := by
  obtain ⟨x, rfl⟩ := homologyClass_surjective f I U n x
  rw [homologyClass_restrict, openEquiv_homologyClass, openEquiv_homologyClass,
    sectionClass_restrict]

/-- Coefficient change and open restriction commute with the same comparison. -/
lemma openEquiv_naturality_restrict {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {I : InjectiveResolution F} {J : InjectiveResolution G} {a : F ⟶ G}
    (φ : I.Hom J a) {V U : Opens Y} (i : V ⟶ U) (n : ℕ)
    (x : (presheaf f I n).obj (op U)) :
    openEquiv f J V n ((presheaf f J n).map i.op ((presheafMap f φ.hom n).app (op U) x)) =
      (G.cohomologyPresheaf n).map ((Opens.map f).map i).op
        (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map a).app
          (op ((Opens.map f).obj U)) (openEquiv f I U n x)) := by
  rw [openEquiv_restrict, openEquiv_naturality]

end FLT.Mazur.HigherDirectImagePresheaf

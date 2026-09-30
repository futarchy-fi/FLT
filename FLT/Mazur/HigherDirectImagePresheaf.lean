/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenModuleDirectImageCohomology
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The presheaf presentation of higher direct images

Sheafification of the homology presheaf of a pushed injective resolution
computes the actual abelian higher direct image. Its sections are additively
identified with inverse-image-open Ext cohomology in every degree. The
identification preserves section cocycles, coefficient maps and Ext universes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex

universe u v

namespace FLT.Mazur.HigherDirectImagePresheaf

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

local instance forgetAdditive {C : Type*} [Category* C] (J : GrothendieckTopology C) :
    (sheafToPresheaf J AddCommGrpCat.{u}).Additive where
  map_add := by intros; rfl

/-- The actual direct image functor on abelian sheaves. -/
abbrev directImage := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f

/-- The presheaf complex underlying the pushed source resolution. -/
def resolutionPresheaf {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) : CochainComplex ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  ((sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (((directImage f).mapHomologicalComplex _).obj I.cocomplex)

/-- A small presheaf presentation using homology of the section complex. -/
def presheaf {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (resolutionPresheaf f I).homology n

/-- Sheafifying the underlying short complex recovers the original sheaf complex. -/
def sheafifiedComplexIso
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) ℕ)
    (n : ℕ) :
    ((K.sc n).map (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})).map
      (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) ≅ K.sc n :=
  ShortComplex.isoMk
    ((asIso (sheafificationAdjunction
      (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).counit).app _)
    ((asIso (sheafificationAdjunction
      (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).counit).app _)
    ((asIso (sheafificationAdjunction
      (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).counit).app _)
    ((sheafificationAdjunction
      (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).counit.naturality _).symm
    ((sheafificationAdjunction
      (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).counit.naturality _).symm

/-- Exact sheafification commutes with homology of the underlying presheaf complex. -/
def sheafificationHomologyIso
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) ℕ) (n : ℕ) :
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
      (((K.sc n).map (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})).homology) ≅
        K.homology n :=
  (((K.sc n).map (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})).mapHomologyIso
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})).symm ≪≫
      (ShortComplex.homologyFunctor _).mapIso (sheafifiedComplexIso K n)

/-- The sheafification comparison is natural in maps of complexes. -/
@[reassoc]
lemma sheafificationHomologyIso_naturality
    {K L : CochainComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) ℕ}
    (φ : K ⟶ L) (n : ℕ) :
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
        (ShortComplex.homologyMap ((sheafToPresheaf
          (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).mapShortComplex.map
          ((shortComplexFunctor _ (ComplexShape.up ℕ) n).map φ))) ≫
        (sheafificationHomologyIso L n).hom =
      (sheafificationHomologyIso K n).hom ≫ homologyMap φ n := by
  dsimp only [sheafificationHomologyIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    ShortComplex.homologyFunctor_obj, ShortComplex.homologyFunctor_map, homology]
  simp only [Category.assoc]
  erw [ShortComplex.mapHomologyIso_inv_naturality_assoc]
  congr 1
  change ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _ =
    ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  congr 1
  ext1 <;> exact (sheafificationAdjunction
    (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).counit.naturality _

/-- The actual higher direct image is the sheafification of the small homology presheaf. -/
def comparison {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) :
    ((directImage f).rightDerived n).obj F ≅
      (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        (presheaf f I n) :=
  I.isoRightDerivedObj (directImage f) n ≪≫
    (sheafificationHomologyIso (((directImage f).mapHomologicalComplex _).obj I.cocomplex) n).symm

/-- A resolution map acts on the homology presheaves. -/
def presheafMap {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) : presheaf f I n ⟶ presheaf f J n :=
  homologyMap
    (((sheafToPresheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}).mapHomologicalComplex _).map
      (((directImage f).mapHomologicalComplex _).map φ)) n

/-- The comparison commutes with coefficient maps and any compatible resolution lift. -/
@[reassoc]
lemma comparison_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {I : InjectiveResolution F} {J : InjectiveResolution G} {a : F ⟶ G}
    (φ : I.Hom J a) (n : ℕ) :
    ((directImage f).rightDerived n).map a ≫ (comparison f J n).hom =
      (comparison f I n).hom ≫
        (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
          (presheafMap f φ.hom n) := by
  dsimp only [comparison, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [I.isoRightDerivedObj_hom_naturality_assoc a J φ.hom
    φ.ι_f_zero_comp_hom_f_zero (directImage f) n]
  congr 1
  rw [← cancel_epi (sheafificationHomologyIso
    (((directImage f).mapHomologicalComplex _).obj I.cocomplex) n).hom]
  simp only [Iso.hom_inv_id_assoc]
  simpa only [Iso.hom_inv_id, Category.comp_id, homologyFunctor_map,
    presheafMap, presheaf, resolutionPresheaf, homologyMap,
    homology, shortComplexFunctor, shortComplexFunctor', Functor.mapShortComplex,
    Functor.mapHomologicalComplex] using
    (sheafificationHomologyIso_naturality_assoc
      (((directImage f).mapHomologicalComplex _).map φ.hom) n
      (sheafificationHomologyIso
        (((directImage f).mapHomologicalComplex _).obj J.cocomplex) n).inv).symm

/-- Canonical homology maps send a represented cycle to its image cycle. -/
lemma homologyMap_cycle {S T : ShortComplex AddCommGrpCat.{u}} (φ : S ⟶ T)
    (x : S.g.hom.ker) (y : T.g.hom.ker) (h : φ.τ₂ x.1 = y.1) :
    ShortComplex.homologyMap φ (S.abHomologyIso.inv (QuotientAddGroup.mk' _ x)) =
      T.abHomologyIso.inv (QuotientAddGroup.mk' _ y) := by
  have hc : ShortComplex.cyclesMap φ (S.abCyclesIso.inv x) = T.abCyclesIso.inv y := by
    apply (AddCommGrpCat.mono_iff_injective T.iCycles).mp inferInstance
    rw [← ConcreteCategory.comp_apply, ShortComplex.cyclesMap_i,
      ConcreteCategory.comp_apply, ShortComplex.abCyclesIso_inv_apply_iCycles,
      ShortComplex.abCyclesIso_inv_apply_iCycles]
    exact h
  have hs := ConcreteCategory.congr_hom S.abLeftHomologyData.π_comp_homologyIso_inv x
  have ht := ConcreteCategory.congr_hom T.abLeftHomologyData.π_comp_homologyIso_inv y
  change S.abHomologyIso.inv (QuotientAddGroup.mk' _ x) =
    S.homologyπ (S.abCyclesIso.inv x) at hs
  change T.abHomologyIso.inv (QuotientAddGroup.mk' _ y) =
    T.homologyπ (T.abCyclesIso.inv y) at ht
  rw [hs, ht, ← ConcreteCategory.comp_apply, ShortComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, hc]

open OpenDirectImageCohomology

local instance sheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) := HasExt.standard _

local instance topSheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} T) := HasExt.standard _

local instance otherTopSheafHasExt (T : TopCat.{u})
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})] :
    HasExt.{v} (TopCat.Sheaf AddCommGrpCat.{u} T) :=
  inferInstanceAs (HasExt.{v} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}))

/-- The short complex of sections on the inverse image of an open. -/
def sectionComplex {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (U : Opens Y) (n : ℕ) : ShortComplex AddCommGrpCat.{u} :=
  ((resolutionPresheaf f I).sc' (n - 1) n (n + 1)).map
    ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (op U))

/-- Evaluation of the homology presheaf is homology of the section complex. -/
def evaluationIso {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (U : Opens Y) (n : ℕ) :
    (sectionComplex f I U n).homology ≅ (presheaf f I n).obj (op U) :=
  (ShortComplex.homologyFunctor _).mapIso
    (((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapShortComplex.mapIso
      ((resolutionPresheaf f I).isoSc' (n - 1) n (n + 1) (show (ComplexShape.up ℕ).prev n = n - 1 by
        cases n <;> simp [CochainComplex.prev_nat_zero, CochainComplex.prev_nat_succ])
        (CochainComplex.next ℕ n)).symm) ≪≫
    ((resolutionPresheaf f I).sc n).mapHomologyIso
      ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (op U))

/-- A map of source resolutions acts on each section complex. -/
def sectionComplexMap {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (U : Opens Y) (n : ℕ) :
    sectionComplex f I U n ⟶ sectionComplex f J U n :=
  ((evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (op U)).mapShortComplex.map
    ((shortComplexFunctor' _ (ComplexShape.up ℕ) (n - 1) n (n + 1)).map
      (((sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).mapHomologicalComplex
        _).map (((directImage f).mapHomologicalComplex _).map φ)))

/-- Evaluation of homology is natural for resolution morphisms. -/
@[reassoc]
lemma evaluationIso_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (U : Opens Y) (n : ℕ) :
    ShortComplex.homologyMap (sectionComplexMap f φ U n) ≫ (evaluationIso f J U n).hom =
      (evaluationIso f I U n).hom ≫ (presheafMap f φ n).app (op U) := by
  let E := (evaluation (Opens Y)ᵒᵖ AddCommGrpCat.{u}).obj (op U)
  let ψ := ((sheafToPresheaf (Opens.grothendieckTopology Y)
    AddCommGrpCat.{u}).mapHomologicalComplex _).map
      (((directImage f).mapHomologicalComplex _).map φ)
  have hi : (ComplexShape.up ℕ).prev n = n - 1 := by
    cases n <;> simp [CochainComplex.prev_nat_zero, CochainComplex.prev_nat_succ]
  have h := congrArg (fun a ↦ ShortComplex.homologyMap (E.mapShortComplex.map a))
    ((natIsoSc' ((Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℕ)
      (n - 1) n (n + 1) hi (CochainComplex.next ℕ n)).inv.naturality ψ)
  dsimp only [evaluationIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, ShortComplex.homologyMap_comp] at h
  simp only [ShortComplex.homologyFunctor_map, Category.assoc]
  erw [← Category.assoc, h, Category.assoc]
  congr 1
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor _ (ComplexShape.up ℕ) n).map ψ) E

/-- Section cocycles present the small homology presheaf. -/
def homologyClass {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (U : Opens Y) (n : ℕ) :
    sectionCycles ((Opens.map f).obj U) I n →+ (presheaf f I n).obj (op U) :=
  (evaluationIso f I U n).hom.hom.comp
    ((sectionComplex f I U n).abHomologyIso.inv.hom.comp
      (QuotientAddGroup.mk' (sectionComplex f I U n).abToCycles.range))

/-- Every section of the homology presheaf is represented by a section cocycle. -/
lemma homologyClass_surjective {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (U : Opens Y) (n : ℕ) :
    Function.Surjective (homologyClass f I U n) :=
  (evaluationIso f I U n).addCommGroupIsoToAddEquiv.surjective.comp
    ((sectionComplex f I U n).abHomologyIso.symm.addCommGroupIsoToAddEquiv.surjective.comp
      (QuotientAddGroup.mk'_surjective (sectionComplex f I U n).abToCycles.range))

/-- The positive-degree kernel consists exactly of section boundaries. -/
lemma homologyClass_eq_zero_iff {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (U : Opens Y) (n : ℕ)
    (x : sectionCycles ((Opens.map f).obj U) I (n + 1)) :
    homologyClass f I U (n + 1) x = 0 ↔
      ∃ y : (I.cocomplex.X n).obj.obj (op ((Opens.map f).obj U)),
        (I.cocomplex.d n (n + 1)).hom.app (op ((Opens.map f).obj U)) y = x.1 := by
  change (evaluationIso f I U (n + 1)).addCommGroupIsoToAddEquiv
    ((sectionComplex f I U (n + 1)).abHomologyIso.symm.addCommGroupIsoToAddEquiv
      (QuotientAddGroup.mk' _ x)) = 0 ↔ _
  rw [AddEquiv.map_eq_zero_iff, AddEquiv.map_eq_zero_iff,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

private lemma extMk_zero_eq_zero_iff {F A : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (a : A ⟶ I.cocomplex.X 0)
    (ha : a ≫ I.cocomplex.d 0 1 = 0) :
    InjectiveResolution.extMk.{u + 1} I a 1 rfl ha = 0 ↔ a = 0 := by
  rw [← (InjectiveResolution.extEquivCohomologyClass.{u + 1} I).apply_eq_iff_eq,
    InjectiveResolution.extEquivCohomologyClass_extMk,
    InjectiveResolution.extEquivCohomologyClass_zero,
    CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff,
    CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _
      (-1) (by omega)]
  constructor
  · rintro ⟨g, hg⟩
    have hg0 : g = 0 := (I.cochainComplex.isZero_of_isStrictlyGE 0 (-1)).eq_of_tgt _ _
    rw [hg0, zero_comp] at hg
    exact (cancel_mono (I.cochainComplexXIso 0 0 rfl).inv).mp (by simpa using hg.symm)
  · rintro rfl
    exact ⟨0, by simp⟩

/-- In degree zero a section cocycle represents zero Ext only if it vanishes. -/
lemma sectionClass_zero_eq_zero_iff {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (U : Opens X) (x : sectionCycles U I 0) :
    sectionClass U I 0 x = 0 ↔ x = 0 := by
  change InjectiveResolution.extMk.{u + 1} I _ 1 rfl (sectionHom_d U I 0 x) = 0 ↔ _
  rw [extMk_zero_eq_zero_iff, AddEquiv.map_eq_zero_iff]
  exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩

/-- There are no boundaries in degree zero of the section complex. -/
lemma homologyClass_zero_eq_zero_iff {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (U : Opens Y)
    (x : sectionCycles ((Opens.map f).obj U) I 0) :
    homologyClass f I U 0 x = 0 ↔ x = 0 := by
  change (evaluationIso f I U 0).addCommGroupIsoToAddEquiv
    ((sectionComplex f I U 0).abHomologyIso.symm.addCommGroupIsoToAddEquiv
      (QuotientAddGroup.mk' _ x)) = 0 ↔ _
  rw [AddEquiv.map_eq_zero_iff, AddEquiv.map_eq_zero_iff,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_range]
  have h : (sectionComplex f I U 0).abToCycles = 0 := by
    ext y
    change (I.cocomplex.d 0 0).hom.app (op ((Opens.map f).obj U)) y = 0
    simp
  simp [h, eq_comm]

/-- In every degree the two cocycle presentations have exactly the same kernel. -/
lemma homologyClass_ker {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (U : Opens Y) (n : ℕ) :
    (homologyClass f I U n).ker = (sectionClass ((Opens.map f).obj U) I n).ker := by
  ext x
  cases n with
  | zero =>
    exact (homologyClass_zero_eq_zero_iff f I U x).trans
      (sectionClass_zero_eq_zero_iff I _ x).symm
  | succ n =>
    exact (homologyClass_eq_zero_iff f I U n x).trans
      (sectionClass_eq_zero_iff _ I n x).symm

/-- Small section-complex homology is actual open Ext cohomology in every degree. -/
def openEquiv {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (U : Opens Y) (n : ℕ) :
    (presheaf f I n).obj (op U) ≃+ Sheaf.H'.{u + 1} F n ((Opens.map f).obj U) :=
  AbsoluteDirectImageCohomology.presentationEquiv
    (homologyClass f I U n) (sectionClass _ I n)
    (homologyClass_surjective f I U n) (sectionClass_surjective _ I n)
    (homologyClass_ker f I U n)

/-- The all-degree comparison preserves the represented section cocycle. -/
@[simp]
lemma openEquiv_homologyClass {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (U : Opens Y) (n : ℕ)
    (x : sectionCycles ((Opens.map f).obj U) I n) :
    openEquiv f I U n (homologyClass f I U n x) = sectionClass _ I n x :=
  AbsoluteDirectImageCohomology.presentationEquiv_apply _ _ _ _ _ _

/-- The standard large Ext groups on inverse-image opens admit the small presentation above. -/
lemma small_openCohomology {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (U : Opens Y) (n : ℕ) :
    Small.{u} (Sheaf.H'.{u + 1} F n ((Opens.map f).obj U)) :=
  small_of_injective (openEquiv f I U n).symm.injective

/-- The small cocycle presentation commutes with resolution morphisms. -/
lemma homologyClass_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (U : Opens Y) (n : ℕ)
    (x : sectionCycles ((Opens.map f).obj U) I n) :
    (presheafMap f φ n).app (op U) (homologyClass f I U n x) =
      homologyClass f J U n (sectionCyclesMap ((Opens.map f).obj U) φ n x) := by
  have h := ConcreteCategory.congr_hom (evaluationIso_naturality f φ U n)
    ((sectionComplex f I U n).abHomologyIso.inv (QuotientAddGroup.mk' _ x))
  change (evaluationIso f J U n).hom _ =
    (presheafMap f φ n).app (op U) (homologyClass f I U n x) at h
  erw [← h, homologyMap_cycle (sectionComplexMap f φ U n) x
    (sectionCyclesMap ((Opens.map f).obj U) φ n x) rfl]
  rfl

/-- The pointwise Ext comparison commutes with coefficient maps. -/
lemma openEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {I : InjectiveResolution F} {J : InjectiveResolution G} {a : F ⟶ G}
    (φ : I.Hom J a) (U : Opens Y) (n : ℕ) (x : (presheaf f I n).obj (op U)) :
    openEquiv f J U n ((presheafMap f φ.hom n).app (op U) x) =
      ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map a).app
        (op ((Opens.map f).obj U)) (openEquiv f I U n x) := by
  obtain ⟨x, rfl⟩ := homologyClass_surjective f I U n x
  rw [homologyClass_naturality, openEquiv_homologyClass, openEquiv_homologyClass,
    sectionClass_naturality]

/-- Changing the Ext universe preserves the represented section cocycle. -/
lemma openEquiv_homologyClass_chgUniv
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (U : Opens Y) (n : ℕ)
    (x : sectionCycles ((Opens.map f).obj U) I n) :
    Abelian.Ext.chgUniv.{v} (openEquiv f I U n (homologyClass f I U n x)) =
      InjectiveResolution.extMk.{v} I
        ((CechFreeOpen.freeOpenHomEquiv _ (I.cocomplex.X n)).symm x.1)
        (n + 1) rfl (sectionHom_d _ I n x) := by
  let := HasDerivedCategory.standard
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  let := HasDerivedCategory.standard (TopCat.Sheaf AddCommGrpCat.{u} X)
  rw [openEquiv_homologyClass]
  apply Abelian.Ext.homEquiv.injective
  rw [Abelian.Ext.homEquiv_chgUniv]
  change (InjectiveResolution.extMk.{u + 1} I _ _ rfl (sectionHom_d _ I n x)).hom =
    (InjectiveResolution.extMk.{v} I _ _ rfl (sectionHom_d _ I n x)).hom
  rw [InjectiveResolution.extMk_hom, InjectiveResolution.extMk_hom]

end FLT.Mazur.HigherDirectImagePresheaf

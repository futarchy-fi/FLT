/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenSheafCohomology
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Exact functors and injective resolution cocycles

An exact additive functor preserving injectives maps injective resolutions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CochainComplex HomComplex

universe w₁ w₂ u

namespace FLT.Mazur.ExactFunctorInjectiveExt

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesInjectiveObjects]
variable {Y : C} (I : InjectiveResolution Y)

/-- Apply an exact functor preserving injectives to a resolution. -/
def imageResolution : InjectiveResolution (F.obj Y) where
  cocomplex := (F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  injective n := F.injective_obj_of_injective (I.injective n)
  ι := (HomologicalComplex.singleMapHomologicalComplex F (.up ℕ) 0).inv.app Y ≫
    (F.mapHomologicalComplex (.up ℕ)).map I.ι

/-- Degreewise comparison for mapping an extension by zero. -/
def mapExtendXIso (K : CochainComplex C ℕ) (i : Option ℕ) :
    F.obj (HomologicalComplex.extend.X K i) ≅
      HomologicalComplex.extend.X ((F.mapHomologicalComplex (.up ℕ)).obj K) i :=
  match i with
  | some _ => Iso.refl _
  | none => (Functor.mapZeroObject F)

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesInjectiveObjects] in
@[reassoc]
lemma mapExtendXIso_hom_d (K : CochainComplex C ℕ) (i j : Option ℕ) :
    (mapExtendXIso F K i).hom ≫
        HomologicalComplex.extend.d ((F.mapHomologicalComplex (.up ℕ)).obj K) i j =
      F.map (HomologicalComplex.extend.d K i j) ≫ (mapExtendXIso F K j).hom := by
  cases i <;> cases j <;> simp [mapExtendXIso, HomologicalComplex.extend.d]

/-- Mapping a complex commutes with extension by zero to integer degrees. -/
def mapExtendIso (K : CochainComplex C ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ mapExtendXIso F K (ComplexShape.embeddingUpNat.r i))
    (fun _ _ _ ↦ mapExtendXIso_hom_d F K _ _)

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesInjectiveObjects] in
@[reassoc]
lemma mapExtendXIso_hom_XIso (K : CochainComplex C ℕ) {i : Option ℕ} {n : ℕ}
    (h : i = some n) :
    (mapExtendXIso F K i).hom ≫
        (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex (.up ℕ)).obj K) h).hom =
      F.map (HomologicalComplex.extend.XIso K h).hom := by
  subst i
  simp [mapExtendXIso, HomologicalComplex.extend.XIso]

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesInjectiveObjects] in
@[reassoc (attr := simp)]
lemma mapExtendIso_hom_f (K : CochainComplex C ℕ) (n : ℕ) :
    (mapExtendIso F K).hom.f n ≫
        (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso
          ComplexShape.embeddingUpNat rfl).hom =
      F.map ((K.extendXIso ComplexShape.embeddingUpNat rfl).hom) :=
  mapExtendXIso_hom_XIso F K _

@[simp]
lemma imageResolution_ι_zero :
    (imageResolution F I).ι.f 0 = F.map (I.ι.f 0) := by
  simp [imageResolution, HomologicalComplex.singleMapHomologicalComplex_inv_app_self]


@[reassoc]
lemma imageResolution_ι' :
    (imageResolution F I).ι' = (F.mapCochainComplexSingleFunctor 0).inv.app Y ≫
      (F.mapHomologicalComplex (.up ℤ)).map I.ι' ≫ (mapExtendIso F I.cocomplex).hom := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    InjectiveResolution.ι'_f_zero, InjectiveResolution.ι'_f_zero]
  simp only [imageResolution_ι_zero,
    Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self, F.map_comp,
    Category.assoc]
  simp only [← F.map_comp_assoc, Iso.inv_hom_id_assoc]
  simp only [F.map_comp, Category.assoc]
  change _ ≫ _ ≫ _ = _ ≫ _ ≫ F.map _ ≫ (mapExtendIso F I.cocomplex).hom.f 0
  rw [← cancel_mono ((imageResolution F I).cochainComplexXIso 0 0 rfl).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change _ = _ ≫ _ ≫ F.map _ ≫ (mapExtendIso F I.cocomplex).hom.f 0 ≫
    (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendXIso
      ComplexShape.embeddingUpNat rfl).hom
  erw [mapExtendIso_hom_f F I.cocomplex 0, ← F.map_comp]
  simp [InjectiveResolution.cochainComplexXIso]

/-- The integer complex of the image resolution is the image integer complex. -/
def imageCochainIso :
    (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex ≅
      (imageResolution F I).cochainComplex := mapExtendIso F I.cocomplex

@[reassoc (attr := simp)]
lemma imageCochainIso_hom_f (n : ℕ) :
    F.map (I.cochainComplexXIso n n rfl).inv ≫ (imageCochainIso F I).hom.f n =
      ((imageResolution F I).cochainComplexXIso n n rfl).inv := by
  rw [← cancel_mono ((imageResolution F I).cochainComplexXIso n n rfl).hom]
  simp only [Category.assoc, Iso.inv_hom_id]
  change _ ≫ (mapExtendIso F I.cocomplex).hom.f n ≫
    (((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendXIso
      ComplexShape.embeddingUpNat rfl).hom = _
  erw [mapExtendIso_hom_f F I.cocomplex n, ← F.map_comp]
  simp [InjectiveResolution.cochainComplexXIso]

/-- A resolution cocycle viewed as a morphism into a shifted integer complex. -/
def cocycleHom {X : C} {n : ℕ} (a : X ⟶ I.cocomplex.X n)
    (ha : a ≫ I.cocomplex.d n (n + 1) = 0) :
    (singleFunctor C 0).obj X ⟶ I.cochainComplex⟦(n : ℤ)⟧ :=
  Cocycle.equivHomShift.symm (Cocycle.fromSingleMk
    (a ≫ (I.cochainComplexXIso n n rfl).inv) (zero_add _) (n + 1)
    (by lia) (by simp [I.cochainComplex_d (n : ℤ) (n + 1 : ℤ) n (n + 1) rfl (by simp),
      reassoc_of% ha]))

@[reassoc]
lemma map_cocycleHom {X : C} {n : ℕ} (a : X ⟶ I.cocomplex.X n)
    (ha : a ≫ I.cocomplex.d n (n + 1) = 0) :
    (F.mapCochainComplexSingleFunctor 0).inv.app X ≫
      ShiftedHom.map (cocycleHom I a ha) (F.mapHomologicalComplex (.up ℤ)) ≫
        (imageCochainIso F I).hom⟦(n : ℤ)⟧' =
      cocycleHom (imageResolution F I) (F.map a) (by
        change F.map a ≫ F.map _ = 0
        rw [← F.map_comp, ha, F.map_zero]) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [ShiftedHom.map, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  have h := HomologicalComplex.XIsoOfEq_inv_naturality
    (imageCochainIso F I).hom (zero_add (n : ℤ))
  have h' : F.map (I.cochainComplex.XIsoOfEq (zero_add (n : ℤ))).inv ≫
      (imageCochainIso F I).hom.f (0 + n) =
      (imageCochainIso F I).hom.f n ≫
        ((imageResolution F I).cochainComplex.XIsoOfEq (zero_add (n : ℤ))).inv := by
    simpa only [HomologicalComplex.XIsoOfEq, eqToIso.inv, eqToHom_map] using h.symm
  simp [cocycleHom, Cocycle.equivHomShift_symm_apply, Cochain.rightShift_v, h',
    imageCochainIso_hom_f_assoc]

open CategoryTheory.Localization

lemma extMk_postcomp [HasExt.{w₁} C] {X : C} {n : ℕ}
    (a : X ⟶ I.cocomplex.X n) (ha : a ≫ I.cocomplex.d n (n + 1) = 0) :
    SmallShiftedHom.comp (I.extMk a (n + 1) rfl ha)
      (SmallShiftedHom.mk₀ (HomologicalComplex.quasiIso C (.up ℤ)) 0 rfl I.ι')
      (zero_add (n : ℤ)) =
      SmallShiftedHom.mk _ (cocycleHom I a ha) := by
  simp [InjectiveResolution.extMk, InjectiveResolution.extEquivCohomologyClass,
    SmallShiftedHom.postcompEquiv, SmallShiftedHom.comp_assoc,
    CohomologyClass.equivOfIsKInjective,
    CohomologyClass.toSmallShiftedHom_mk, cocycleHom]

/-- Exact functors carry resolution cocycles to the corresponding image classes,
including degree zero. The two Ext universes may differ. -/
lemma mapExactFunctor_extMk [HasExt.{w₁} C] [HasExt.{w₂} D] {X : C} {n : ℕ}
    (a : X ⟶ I.cocomplex.X n) (ha : a ≫ I.cocomplex.d n (n + 1) = 0) :
    (I.extMk a (n + 1) rfl ha).mapExactFunctor F =
      (imageResolution F I).extMk (F.map a) (n + 1) rfl (by
        change F.map a ≫ F.map _ = 0
        rw [← F.map_comp, ha, F.map_zero]) := by
  let Φ := F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (.up ℤ)
  let eX : Φ.functor.obj ((singleFunctor C 0).obj X) ≅
      (singleFunctor D 0).obj (F.obj X) := (F.mapCochainComplexSingleFunctor 0).app X
  let eY : Φ.functor.obj ((singleFunctor C 0).obj Y) ≅
      (singleFunctor D 0).obj (F.obj Y) := (F.mapCochainComplexSingleFunctor 0).app Y
  have h := Φ.smallShiftedHomMap_comp eX eY (imageCochainIso F I)
    (I.extMk a (n + 1) rfl ha)
    (SmallShiftedHom.mk₀ (HomologicalComplex.quasiIso C (.up ℤ)) 0 rfl I.ι')
    (zero_add (n : ℤ))
  rw [extMk_postcomp, Φ.smallShiftedHomMap_mk, Φ.smallShiftedHomMap_mk₀] at h
  have hi : eY.inv ≫
      Φ.functor.map I.ι' ≫ (imageCochainIso F I).hom = (imageResolution F I).ι' :=
    (imageResolution_ι' F I).symm
  erw [hi] at h
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] at h
  have hc : eX.inv ≫ ShiftedHom.map (cocycleHom I a ha) Φ.functor ≫
      (imageCochainIso F I).hom⟦(n : ℤ)⟧' =
      cocycleHom (imageResolution F I) (F.map a) (by
        change F.map a ≫ F.map _ = 0
        rw [← F.map_comp, ha, F.map_zero]) := map_cocycleHom F I a ha
  rw [hc] at h
  apply (SmallShiftedHom.postcompEquiv (imageResolution F I).ι'
    (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)).injective
  change SmallShiftedHom.comp _ _ _ = SmallShiftedHom.comp _ _ _
  rw [extMk_postcomp]
  exact h.symm

/-- The Ext adjunction acts on resolution cocycles by its Hom adjunction. -/
lemma extEquiv_extMk {L : D ⥤ C} [L.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [HasExt.{w₁} C] [HasExt.{w₂} D] (adj : L ⊣ F) {X : D} {n : ℕ}
    (a : L.obj X ⟶ I.cocomplex.X n) (ha : a ≫ I.cocomplex.d n (n + 1) = 0) :
    adj.extEquiv (I.extMk a (n + 1) rfl ha) =
      (imageResolution F I).extMk (adj.homEquiv _ _ a) (n + 1) rfl (by
        rw [Adjunction.homEquiv_unit]
        change (adj.unit.app X ≫ F.map a) ≫ F.map _ = 0
        rw [Category.assoc, ← F.map_comp, ha, F.map_zero, comp_zero]) := by
  rw [Adjunction.extEquiv_apply, mapExactFunctor_extMk,
    InjectiveResolution.mk₀_comp_extMk]
  rfl

section Restriction

open TopologicalSpace Opposite OpenSheafRestriction OpenSheafFreeComparison CechFreeOpen

local instance sheafHasExt (X : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := HasExt.standard _

local instance topSheafHasExt (X : TopCat.{u}) :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) := HasExt.standard _

variable {T : TopCat.{u}} (W : Opens T) {A : TopCat.Sheaf AddCommGrpCat.{u} T}
  (J : InjectiveResolution A) {n : ℕ}

local instance restrictedHasExt :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- Restriction sends an open section cocycle to its adjoint cocycle. -/
lemma openHEquiv_extMk (a : freeOpen W ⟶ J.cocomplex.X n)
    (ha : a ≫ J.cocomplex.d n (n + 1) = 0) :
    OpenSheafCohomology.openHEquiv.{u, u + 1} W A n (J.extMk a (n + 1) rfl ha) =
      (imageResolution (restriction W) J).extMk
        ((adjunction W).homEquiv _ _ ((extensionFreeOpenIso W).hom ≫ a))
        (n + 1) rfl (by
          rw [Adjunction.homEquiv_unit]
          change (_ ≫ (restriction W).map _) ≫ (restriction W).map _ = 0
          rw [Category.assoc, ← Functor.map_comp, Category.assoc, ha,
            comp_zero, Functor.map_zero, comp_zero]) := by
  change (adjunction W).extEquiv
    ((Ext.mk₀ (extensionFreeOpenIso W).hom).comp
      (J.extMk a (n + 1) rfl ha) (zero_add n)) = _
  rw [InjectiveResolution.mk₀_comp_extMk]
  exact extEquiv_extMk (restriction W) J (adjunction W) _ _

/-- The cocycle in `openHEquiv_extMk` represents precisely the original section. -/
lemma openHEquiv_extMk_section (a : freeOpen W ⟶ J.cocomplex.X n) :
    (restrictionTopIso W (J.cocomplex.X n)).hom
      (constantIntegerHomEquiv _
        ((adjunction W).homEquiv _ _ ((extensionFreeOpenIso W).hom ≫ a))) =
      freeOpenHomEquiv W (J.cocomplex.X n) a :=
  extensionFreeOpenIso_hom_evaluation W _ a

end Restriction

end FLT.Mazur.ExactFunctorInjectiveExt

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HigherDirectImagePresheafRestriction
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Higher direct images as sheafified open cohomology

A small presentation of actual inverse-image-open Ext cohomology sheafifies
to the actual abelian higher direct image. For module coefficients its values
are the cohomology of restricted modules, with their local scalar actions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u v

namespace FLT.Mazur.HigherDirectImageOpenSheafification

open HigherDirectImagePresheaf OpenDirectImageCohomology

local instance sheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) := HasExt.standard _

local instance topSheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} T) := HasExt.standard _

local instance otherTopSheafHasExt (T : TopCat.{u})
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})] :
    HasExt.{v} (TopCat.Sheaf AddCommGrpCat.{u} T) :=
  inferInstanceAs (HasExt.{v} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}))

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

local instance openSmall (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : Opens Y) (n : ℕ) :
    Small.{u} (Sheaf.H'.{u + 1} F n ((Opens.map f).obj U)) :=
  small_openCohomology f (injectiveResolution F) U n

/-- The actual open Ext presheaf, explicitly shrunk to the coefficient universe. -/
def openPresheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (Shrink.{u} (Sheaf.H'.{u + 1} F n ((Opens.map f).obj U.unop)))
  map i := AddCommGrpCat.ofHom
    ((Shrink.addEquiv.symm.toAddMonoidHom.comp
      ((F.cohomologyPresheaf n).map ((Opens.map f).map i.unop).op).hom).comp
        Shrink.addEquiv.toAddMonoidHom)
  map_id U := by ext x; simp
  map_comp i j := by ext x; simp [Functor.map_comp]

/-- Decoding a small value gives actual open Ext cohomology. -/
def openValueEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : Opens Y) (n : ℕ) :
    (openPresheaf f F n).obj (op U) ≃+ Sheaf.H'.{u + 1} F n ((Opens.map f).obj U) :=
  Shrink.addEquiv

/-- Decoding preserves the existing Ext restriction maps. -/
lemma openValueEquiv_restrict (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {V U : Opens Y} (i : V ⟶ U) (n : ℕ) (x : (openPresheaf f F n).obj (op U)) :
    openValueEquiv f F V n ((openPresheaf f F n).map i.op x) =
      (F.cohomologyPresheaf n).map ((Opens.map f).map i).op (openValueEquiv f F U n x) :=
  Shrink.addEquiv.apply_symm_apply _

/-- The cocycle comparison is an honest isomorphism of small presheaves. -/
def openPresheafIso {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) : presheaf f I n ≅ openPresheaf f F n :=
  NatIso.ofComponents
    (fun U ↦ ((openEquiv f I U.unop n).trans (openValueEquiv f F U.unop n).symm).toAddCommGrpIso)
    (fun {U V} i ↦ by
      ext x
      change (openValueEquiv f F V.unop n).symm
          (openEquiv f I V.unop n ((presheaf f I n).map i x)) =
        (openValueEquiv f F V.unop n).symm
          ((F.cohomologyPresheaf n).map ((Opens.map f).map i.unop).op
            ((openValueEquiv f F U.unop n)
              ((openValueEquiv f F U.unop n).symm (openEquiv f I U.unop n x))))
      rw [AddEquiv.apply_symm_apply]
      exact congrArg (openValueEquiv f F V.unop n).symm (openEquiv_restrict f I i.unop n x))

/-- Higher direct images are sheafifications of actual inverse-image-open cohomology. -/
def openComparison {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) :
    ((directImage f).rightDerived n).obj F ≅
      (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        (openPresheaf f F n) :=
  comparison f I n ≪≫
    (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).mapIso
      (openPresheafIso f I n)

/-- Coefficient maps on the actual open cohomology presentation. -/
def openPresheafMap {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (a : F ⟶ G) (n : ℕ) :
    openPresheaf f F n ⟶ openPresheaf f G n where
  app U := AddCommGrpCat.ofHom
    (((openValueEquiv f G U.unop n).symm.toAddMonoidHom.comp
      (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map a).app
        (op ((Opens.map f).obj U.unop))).hom).comp
      (openValueEquiv f F U.unop n).toAddMonoidHom)
  naturality U V i := by
    ext x
    let α := (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map a
    let eF := fun W : (Opens Y)ᵒᵖ ↦ openValueEquiv f F W.unop n
    let eG := fun W : (Opens Y)ᵒᵖ ↦ openValueEquiv f G W.unop n
    let j := ((Opens.map f).map i.unop).op
    change (eG V).symm (α.app _ (eF V ((eF V).symm
        ((F.cohomologyPresheaf n).map j (eF U x))))) =
      (eG V).symm ((G.cohomologyPresheaf n).map j
        (eG U ((eG U).symm (α.app _ (eF U x)))))
    rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact congrArg (eG V).symm (ConcreteCategory.congr_hom (α.naturality j) (eF U x))

/-- The presheaf comparison is natural in coefficients and compatible resolution lifts. -/
@[reassoc]
lemma openPresheafIso_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {I : InjectiveResolution F} {J : InjectiveResolution G} {a : F ⟶ G}
    (φ : I.Hom J a) (n : ℕ) :
    presheafMap f φ.hom n ≫ (openPresheafIso f J n).hom =
      (openPresheafIso f I n).hom ≫ openPresheafMap f a n := by
  ext U x
  apply (openValueEquiv f G U.unop n).injective
  simpa [openPresheafIso, openPresheafMap] using openEquiv_naturality f φ U.unop n x

/-- The sheafification statement retains coefficient naturality. -/
@[reassoc]
lemma openComparison_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {I : InjectiveResolution F} {J : InjectiveResolution G} {a : F ⟶ G}
    (φ : I.Hom J a) (n : ℕ) :
    ((directImage f).rightDerived n).map a ≫ (openComparison f J n).hom =
      (openComparison f I n).hom ≫
        (presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).map
          (openPresheafMap f a n) := by
  simp only [openComparison, Iso.trans_hom, Functor.mapIso_hom, ← Category.assoc]
  rw [comparison_naturality f φ n]
  simp only [Category.assoc, ← Functor.map_comp, openPresheafIso_naturality f φ n]

/-- The small presentation retains the canonical change-of-Ext-universe cocycle formula. -/
lemma openPresheafIso_chgUniv
    [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (U : Opens Y) (n : ℕ) (x : sectionCycles ((Opens.map f).obj U) I n) :
    Abelian.Ext.chgUniv.{v} (openValueEquiv f F U n
      ((openPresheafIso f I n).hom.app (op U) (homologyClass f I U n x))) =
      InjectiveResolution.extMk.{v} I
        ((CechFreeOpen.freeOpenHomEquiv _ (I.cocomplex.X n)).symm x.1)
        (n + 1) rfl (sectionHom_d _ I n x) := by
  simpa [openPresheafIso] using openEquiv_homologyClass_chgUniv f I U n x

open FCurve

/-- For schemes the small values compute actual cohomology of restricted modules. -/
def moduleValueEquiv {S T : Scheme.{u}} (g : S ⟶ T) (M : S.Modules)
    (U : T.Opens) (n : ℕ) :
    (openPresheaf g.base (moduleAbelianSheaf M) n).obj (op U) ≃+
      ModuleH (M.restrict (g ⁻¹ᵁ U).ι) n :=
  (openValueEquiv g.base (moduleAbelianSheaf M) U n).trans
    (moduleOpenHEquiv (g ⁻¹ᵁ U) M n)

/-- The small module presentation uses the existing module open restriction. -/
lemma moduleValueEquiv_restrict {S T : Scheme.{u}} (g : S ⟶ T) (M : S.Modules)
    {V U : T.Opens} (i : V ⟶ U) (n : ℕ)
    (x : (openPresheaf g.base (moduleAbelianSheaf M) n).obj (op U)) :
    moduleValueEquiv g M V n ((openPresheaf g.base (moduleAbelianSheaf M) n).map i.op x) =
      moduleOpenRestriction M ((Opens.map g.base).map i) n (moduleValueEquiv g M U n x) := by
  change moduleOpenHEquiv (g ⁻¹ᵁ V) M n
      (openValueEquiv g.base (moduleAbelianSheaf M) V n
        ((openPresheaf g.base (moduleAbelianSheaf M) n).map i.op x)) =
    moduleOpenHEquiv (g ⁻¹ᵁ V) M n
      (((moduleAbelianSheaf M).cohomologyPresheaf n).map ((Opens.map g.base).map i).op
        ((moduleOpenHEquiv (g ⁻¹ᵁ U) M n).symm
          (moduleOpenHEquiv (g ⁻¹ᵁ U) M n (openValueEquiv g.base (moduleAbelianSheaf M) U n x))))
  rw [AddEquiv.symm_apply_apply]
  exact congrArg (moduleOpenHEquiv (g ⁻¹ᵁ V) M n)
    (openValueEquiv_restrict g.base (moduleAbelianSheaf M) i n x)

/-- Local section scalars on the small presentation are transported from actual module H. -/
abbrev moduleValueModule {S T : Scheme.{u}} (g : S ⟶ T) (M : S.Modules)
    (U : T.Opens) (n : ℕ) :
    Module Γ((g ⁻¹ᵁ U).toScheme, ⊤)
      ((openPresheaf g.base (moduleAbelianSheaf M) n).obj (op U)) :=
  (moduleValueEquiv g M U n).module _

/-- The value comparison respects every local section scalar. -/
def moduleValueLinearEquiv {S T : Scheme.{u}} (g : S ⟶ T) (M : S.Modules)
    (U : T.Opens) (n : ℕ) :
    letI := moduleValueModule g M U n
    (openPresheaf g.base (moduleAbelianSheaf M) n).obj (op U) ≃ₗ[Γ((g ⁻¹ᵁ U).toScheme, ⊤)]
      ModuleH (M.restrict (g ⁻¹ᵁ U).ι) n :=
  (moduleValueEquiv g M U n).linearEquiv _

/-- Restriction is semilinear over restriction of local sections. -/
lemma moduleValue_restrict_smul {S T : Scheme.{u}} (g : S ⟶ T) (M : S.Modules)
    {V U : T.Opens} (i : V ⟶ U) (n : ℕ) (r : Γ((g ⁻¹ᵁ U).toScheme, ⊤))
    (x : (openPresheaf g.base (moduleAbelianSheaf M) n).obj (op U)) :
    letI := moduleValueModule g M U n
    letI := moduleValueModule g M V n
    (openPresheaf g.base (moduleAbelianSheaf M) n).map i.op (r • x) =
      (S.homOfLE (leOfHom ((Opens.map g.base).map i))).appTop r •
        (openPresheaf g.base (moduleAbelianSheaf M) n).map i.op x := by
  let := moduleValueModule g M U n
  let := moduleValueModule g M V n
  apply (moduleValueEquiv g M V n).injective
  rw [moduleValueEquiv_restrict]
  change moduleOpenRestriction M _ n (moduleValueLinearEquiv g M U n (r • x)) =
    moduleValueLinearEquiv g M V n (_ • _)
  rw [map_smul (moduleValueLinearEquiv g M U n), map_smul (moduleValueLinearEquiv g M V n),
    moduleOpenRestriction_smul]
  exact congrArg (fun z ↦ (S.homOfLE (leOfHom ((Opens.map g.base).map i))).appTop r • z)
    (moduleValueEquiv_restrict g M i n x).symm

/-- The actual restricted-module value comparison is natural in coefficients. -/
lemma moduleValueEquiv_naturality {S T : Scheme.{u}} (g : S ⟶ T)
    {M N : S.Modules} (a : M ⟶ N) (U : T.Opens) (n : ℕ)
    (x : (openPresheaf g.base (moduleAbelianSheaf M) n).obj (op U)) :
    moduleValueEquiv g N U n
      ((openPresheafMap g.base ((SheafOfModules.toSheaf S.ringCatSheaf).map a) n).app (op U) x) =
      moduleHMap ((Scheme.Modules.restrictFunctor (g ⁻¹ᵁ U).ι).map a) n
        (moduleValueEquiv g M U n x) := by
  simpa [moduleValueEquiv, openPresheafMap] using
    moduleOpenHEquiv_naturality (g ⁻¹ᵁ U) a n (openValueEquiv g.base (moduleAbelianSheaf M) U n x)

/-- The scheme/module version of the abelian higher-image sheafification statement. -/
def moduleOpenComparison {S T : Scheme.{u}} (g : S ⟶ T) (M : S.Modules) (n : ℕ) :
    ((directImage g.base).rightDerived n).obj (moduleAbelianSheaf M) ≅
      (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}).obj
        (openPresheaf g.base (moduleAbelianSheaf M) n) :=
  openComparison g.base (injectiveResolution (moduleAbelianSheaf M)) n

end FLT.Mazur.HigherDirectImageOpenSheafification

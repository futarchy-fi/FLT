/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenDirectImageRestriction
public import FLT.Mazur.SchemeCohomologyIso

/-!
# Cohomology presheaves under open restriction

Extension of a free-open sheaf represents sections on the image open.
The Ext adjunction therefore compares cohomology on every subspace open,
with its restriction and coefficient maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite

universe u w₁ w₂

namespace FLT.Mazur.OpenSheafCohomologyRestriction

open OpenSheafRestriction CechFreeOpen ExactFunctorInjectiveExt
open AffineCohomologyVanishingLocal

section Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasExt.{w₁} C] [HasExt.{w₂} D] {L : C ⥤ D} {R : D ⥤ C}
  [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- The Ext adjunction after identifying its represented source by an isomorphism. -/
def adjunctionIsoExtEquiv (adj : L ⊣ R) {A : C} {B : D} (e : L.obj A ≅ B)
    (F : D) (n : ℕ) : Ext B F n ≃+ Ext A (R.obj F) n :=
  (((Abelian.extFunctor n).mapIso e.op).app F).addCommGroupIsoToAddEquiv.trans adj.extEquiv

lemma adjunctionIsoExtEquiv_apply (adj : L ⊣ R) {A : C} {B : D} (e : L.obj A ≅ B)
    (F : D) (n : ℕ) (x : Ext B F n) :
    adjunctionIsoExtEquiv adj e F n x =
      adj.extEquiv ((Ext.mk₀ e.hom).comp x (zero_add n)) := rfl

end Adjunction

variable {X : TopCat.{u}} (U : Opens X) (V : Opens U)

/-- Extension of a free-open sheaf represents sections on the ambient image. -/
def extensionHomEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((extension U).obj (freeOpen (X := TopCat.of U) V) ⟶ F) ≃
      (freeOpen ((openImage U).obj V) ⟶ F) :=
  ((adjunction U).homEquiv _ F).trans
    ((freeOpenHomEquiv (X := TopCat.of U) V ((restriction U).obj F)).toEquiv.trans
      (freeOpenHomEquiv ((openImage U).obj V) F).toEquiv.symm)

lemma extensionHomEquiv_evaluation (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (a : (extension U).obj (freeOpen (X := TopCat.of U) V) ⟶ F) :
    freeOpenHomEquiv ((openImage U).obj V) F (extensionHomEquiv U V F a) =
      freeOpenHomEquiv (X := TopCat.of U) V ((restriction U).obj F)
        ((adjunction U).homEquiv _ _ a) :=
  (freeOpenHomEquiv ((openImage U).obj V) F).apply_symm_apply _

lemma extensionHomEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (a : (extension U).obj (freeOpen (X := TopCat.of U) V) ⟶ F) :
    extensionHomEquiv U V G (a ≫ f) = extensionHomEquiv U V F a ≫ f := by
  apply (freeOpenHomEquiv ((openImage U).obj V) G).injective
  rw [extensionHomEquiv_evaluation, freeOpenHomEquiv_naturality,
    extensionHomEquiv_evaluation, Adjunction.homEquiv_naturality_right,
    freeOpenHomEquiv_naturality]
  rfl

/-- Extension carries a subspace free-open sheaf to the free sheaf on its image. -/
def extensionFreeIso :
    (extension U).obj (freeOpen (X := TopCat.of U) V) ≅ freeOpen ((openImage U).obj V) where
  hom := (extensionHomEquiv U V _).symm (𝟙 _)
  inv := extensionHomEquiv U V _ (𝟙 _)
  hom_inv_id := by
    apply (extensionHomEquiv U V _).injective
    rw [extensionHomEquiv_naturality]
    simp only [Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := extensionHomEquiv_naturality U V
      ((extensionHomEquiv U V _).symm (𝟙 _)) (𝟙 _)
    simpa only [Category.id_comp, Equiv.apply_symm_apply] using h.symm

/-- The adjoint of the comparison preserves the represented section. -/
lemma extensionFreeIso_evaluation (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (a : freeOpen ((openImage U).obj V) ⟶ F) :
    freeOpenHomEquiv (X := TopCat.of U) V ((restriction U).obj F)
      ((adjunction U).homEquiv _ _ ((extensionFreeIso U V).hom ≫ a)) =
      freeOpenHomEquiv ((openImage U).obj V) F a := by
  rw [← extensionHomEquiv_evaluation, extensionHomEquiv_naturality]
  change freeOpenHomEquiv ((openImage U).obj V) F
    ((extensionHomEquiv U V _) ((extensionHomEquiv U V _).symm (𝟙 _)) ≫ a) = _
  rw [Equiv.apply_symm_apply, Category.id_comp]

local instance sheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) := HasExt.standard _

local instance topSheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} T) := HasExt.standard _

local instance restrictedHasExt :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology U) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- Ambient image-open cohomology equals subspace-open cohomology. -/
def imageHEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Sheaf.H'.{u + 1} F n ((openImage U).obj V) ≃+
      Sheaf.H'.{u + 1} ((restriction U).obj F) n V :=
  adjunctionIsoExtEquiv.{u + 1, u + 1} (adjunction (X := X) U)
    (extensionFreeIso (X := X) U V) F n

lemma imageHEquiv_apply (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ)
    (x : Sheaf.H'.{u + 1} F n ((openImage U).obj V)) :
    imageHEquiv U V F n x =
      (adjunction U).extEquiv
        ((Ext.mk₀ (extensionFreeIso U V).hom).comp x (zero_add n)) :=
  adjunctionIsoExtEquiv_apply (adjunction U) (extensionFreeIso U V) F n x

/-- The image-open comparison commutes with coefficient morphisms. -/
lemma imageHEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) (x : Sheaf.H'.{u + 1} F n ((openImage U).obj V)) :
    imageHEquiv U V G n
        (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map f).app
          (op ((openImage U).obj V)) x) =
      ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology U) n).map
        ((restriction U).map f)).app (op V) (imageHEquiv U V F n x) := by
  rw [imageHEquiv_apply, imageHEquiv_apply]
  change (adjunction U).extEquiv
      ((Ext.mk₀ (extensionFreeIso U V).hom).comp
        (x.comp (Ext.mk₀ f) (add_zero n)) (zero_add n)) = _
  rw [← Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)]
  exact Adjunction.extEquiv_naturality_right₀ (adjunction U) _ f

open OpenDirectImageCohomology OpenDirectImageNaturality

/-- The image-open comparison preserves the section cocycle in every degree. -/
lemma imageHEquiv_sectionClass {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ)
    (x : sectionCycles ((openImage U).obj V) I n) :
    imageHEquiv U V F n (sectionClass ((openImage U).obj V) I n x) =
      sectionClass (X := TopCat.of U) V (imageResolution (restriction U) I) n x := by
  rw [imageHEquiv_apply]
  change (adjunction U).extEquiv
    ((Ext.mk₀ (extensionFreeIso U V).hom).comp (I.extMk _ _ rfl
      (sectionHom_d ((openImage U).obj V) I n x)) (zero_add n)) = _
  refine (congrArg (adjunction U).extEquiv
    (InjectiveResolution.mk₀_comp_extMk.{u + 1} I
      ((freeOpenHomEquiv ((openImage U).obj V) (I.cocomplex.X n)).symm x.1)
      (n + 1) rfl (sectionHom_d ((openImage U).obj V) I n x)
      (extensionFreeIso U V).hom)).trans ?_
  refine (extEquiv_extMk (restriction U) I (adjunction U) _ _).trans ?_
  have h : (adjunction U).homEquiv _ _ ((extensionFreeIso U V).hom ≫
      (freeOpenHomEquiv ((openImage U).obj V) (I.cocomplex.X n)).symm x.1) =
      (freeOpenHomEquiv (X := TopCat.of U) V ((restriction U).obj (I.cocomplex.X n))).symm x.1 := by
    apply (freeOpenHomEquiv (X := TopCat.of U) V _).injective
    rw [extensionFreeIso_evaluation, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp only [sectionClass, AddMonoidHom.coe_mk, h]
  rfl

/-- The comparison commutes with every inclusion of subspace opens. -/
private lemma imageHEquiv_restrict_aux (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (I : InjectiveResolution F)
    {V W : Opens U} (i : V ⟶ W) (n : ℕ)
    (x : Sheaf.H'.{u + 1} F n ((openImage U).obj W)) :
    imageHEquiv U V F n ((Sheaf.cohomologyPresheaf.{u + 1} F n).map ((openImage U).map i).op x) =
      (Sheaf.cohomologyPresheaf.{u + 1} ((restriction U).obj F) n).map i.op
        (imageHEquiv U W F n x) := by
  obtain ⟨x, rfl⟩ := sectionClass_surjective _ I n x
  refine (congrArg (imageHEquiv U V F n)
    (sectionClass_restrict I ((openImage U).map i) n x)).trans ?_
  refine (imageHEquiv_sectionClass U V I n _).trans ?_
  exact (sectionClass_restrict (imageResolution (restriction U) I) i n x).symm.trans
    (congrArg ((Sheaf.cohomologyPresheaf.{u + 1} ((restriction U).obj F) n).map i.op)
      (imageHEquiv_sectionClass U W I n x).symm)

lemma imageHEquiv_restrict (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {V W : Opens U} (i : V ⟶ W) (n : ℕ)
    (x : Sheaf.H'.{u + 1} F n ((openImage U).obj W)) :
    imageHEquiv U V F n
        ((Sheaf.cohomologyPresheaf.{u + 1} F n).map ((openImage U).map i).op x) =
      (Sheaf.cohomologyPresheaf.{u + 1} ((restriction U).obj F) n).map i.op
        (imageHEquiv U W F n x) :=
  imageHEquiv_restrict_aux U F (injectiveResolution F) i n x

/-- Restriction of global classes is natural for all coefficient morphisms on the space. -/
lemma restrictSheafH_coeff {T : TopCat.{u}} {F G : TopCat.Sheaf AddCommGrpCat.{u} T}
    (f : F ⟶ G) (W : Opens T) (n : ℕ) (x : Sheaf.H F n) :
    restrictSheafH G n W (Sheaf.H.map f n x) =
      ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology T) n).map f).app
        (op W) (restrictSheafH F n W x) := by
  change (Ext.mk₀ (CechFreeResolution.freeOpenAugmentation W)).comp
    (x.comp (Ext.mk₀ f) (add_zero n)) (zero_add n) = _
  exact (Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)).symm

/-- The cocycle formula for restricting a global class to an open. -/
lemma restrictSheafH_sectionClass {T : TopCat.{u}} {F : TopCat.Sheaf AddCommGrpCat.{u} T}
    (I : InjectiveResolution F) (W : Opens T) (n : ℕ)
    (x : AbsoluteDirectImageCohomology.sectionCycles I n) :
    restrictSheafH F n W (AbsoluteDirectImageCohomology.sectionClass I n x) =
      sectionClass W I n (sectionCyclesRestrict I (homOfLE le_top) n x) := by
  rw [← restrictSheafH_naturality F n (homOfLE (show W ≤ ⊤ from le_top)),
    restrictSheafH_top, sheafHTopEquiv_sectionClass, sectionClass_restrict]

/-- The transported ambient restriction is ordinary restriction on the intermediate open. -/
private lemma imageHEquiv_restrict_openHEquiv_aux
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (I : InjectiveResolution F)
    (n : ℕ) (x : Sheaf.H'.{u + 1} F n U) :
    imageHEquiv U V F n
        ((Sheaf.cohomologyPresheaf.{u + 1} F n).map (homOfLE (openImage_le U V)).op x) =
      restrictSheafH (X := TopCat.of U) ((restriction U).obj F) n V
        (OpenSheafCohomology.openHEquiv.{u, u + 1} U F n x) := by
  obtain ⟨x, rfl⟩ := sectionClass_surjective U I n x
  let J := imageResolution (restriction U) I
  refine (congrArg (imageHEquiv U V F n)
    (sectionClass_restrict I (homOfLE (openImage_le U V)) n x)).trans ?_
  refine (imageHEquiv_sectionClass U V I n _).trans ?_
  have hc : (sectionCyclesRestrict I (homOfLE (openImage_le U V)) n x :
      sectionCycles (X := TopCat.of U) V J n) =
      sectionCyclesRestrict J (homOfLE le_top) n
        (OpenDirectImageRestriction.restrictedCycles U I n x) := by
    apply Subtype.ext
    change (I.cocomplex.X n).obj.map _ x.1 =
      (I.cocomplex.X n).obj.map _ ((I.cocomplex.X n).obj.map _ x.1)
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  refine (congrArg (sectionClass (X := TopCat.of U) V J n) hc).trans ?_
  refine (restrictSheafH_sectionClass J V n _).symm.trans ?_
  exact congrArg (restrictSheafH (X := TopCat.of U) ((restriction U).obj F) n V)
    (OpenDirectImageRestriction.openHEquiv_sectionClass U I n x).symm


lemma imageHEquiv_restrict_openHEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (n : ℕ) (x : Sheaf.H'.{u + 1} F n U) :
    imageHEquiv U V F n
        ((Sheaf.cohomologyPresheaf.{u + 1} F n).map (homOfLE (openImage_le U V)).op x) =
      restrictSheafH (X := TopCat.of U) ((restriction U).obj F) n V
        (OpenSheafCohomology.openHEquiv.{u, u + 1} U F n x) :=
  imageHEquiv_restrict_openHEquiv_aux U V F (injectiveResolution F) n x

section Schemes

open AlgebraicGeometry

variable {S : Scheme.{u}} (W : S.Opens) (T : W.toScheme.Opens)

/-- Flattening an iterated open preserves the ambient image of every smaller open. -/
lemma nestedImage_eq (O : T.toScheme.Opens) :
    (openImage (W.ι ''ᵁ T)).obj ((W.ι.isoImage T).hom.opensFunctor.obj O) =
      (openImage W).obj ((openImage T).obj O) := by
  change (W.ι ''ᵁ T).ι ''ᵁ ((W.ι.isoImage T).hom ''ᵁ O) = W.ι ''ᵁ (T.ι ''ᵁ O)
  simp only [← Scheme.Hom.comp_image, Scheme.Hom.isoImage_hom_ι]

/-- The canonical scheme isomorphism identifies direct and iterated sheaf restriction. -/
def nestedRestrictionIso :
    restriction (W.ι ''ᵁ T) ⋙
        (SchemeCohomologyIso.abelianSheafEquivalence (W.ι.isoImage T)).inverse ≅
      restriction W ⋙ restriction T :=
  NatIso.ofComponents (fun F ↦
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (NatIso.ofComponents (fun O ↦
        F.obj.mapIso (eqToIso (nestedImage_eq W T O.unop).symm).op)
        (by
          intro O P i
          change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
          simp only [← F.obj.map_comp]
          congr 1)))
    (by
      intro F G a
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext O
      exact (a.hom.naturality (eqToHom (nestedImage_eq W T O.unop).symm).op).symm)

end Schemes

end FLT.Mazur.OpenSheafCohomologyRestriction

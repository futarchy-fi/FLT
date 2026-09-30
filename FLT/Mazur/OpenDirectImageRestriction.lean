/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ExactFunctorInjectiveExt
public import FLT.Mazur.OpenDirectImageNaturality
public import FLT.Mazur.ClosedPushforwardRestriction

/-!
# Restriction of the acyclic direct-image comparison

Restrict the source and image resolutions to derive local acyclicity.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FLT.Mazur.OpenDirectImageRestriction

open OpenSheafRestriction ExactFunctorInjectiveExt AcyclicDirectImageResolution
open AbsoluteDirectImageCohomology (Acyclic)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- The abelian restriction square, using the same open equality as module pushforward. -/
def pushforwardRestriction :
    TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base ⋙ restriction U ≅
      restriction (f ⁻¹ᵁ U) ⋙ TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ∣_ U).base :=
  NatIso.ofComponents (fun A ↦
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (NatIso.ofComponents (fun V ↦
        A.obj.mapIso (eqToIso (image_morphismRestrict_preimage f U V.unop)).op)
        (by
          intro V W i
          change A.obj.map _ ≫ A.obj.map _ = A.obj.map _ ≫ A.obj.map _
          simp only [← A.obj.map_comp]
          congr 1)))
    (by
      intro A B α
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext V
      exact (α.hom.naturality (eqToHom (image_morphismRestrict_preimage f U V.unop)).op).symm)

/-- The restricted source resolution is chosen internally from the global one. -/
def sourceResolution (A : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat) :
    InjectiveResolution ((restriction (f ⁻¹ᵁ U)).obj A) :=
  imageResolution (restriction (f ⁻¹ᵁ U)) (injectiveResolution A)

/-- The local image complex is isomorphic to the restricted global image resolution. -/
def imageComplexIso (A : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat)
    (hA : Acyclic f.base A) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ∣_ U).base).mapHomologicalComplex
      (.up ℕ)).obj (sourceResolution f U A).cocomplex ≅
      (imageResolution (restriction U) (directImageResolution f.base A hA)).cocomplex :=
  (NatIso.mapHomologicalComplex (pushforwardRestriction f U).symm (.up ℕ)).app
    (injectiveResolution A).cocomplex

/-- Local positive higher images vanish as a consequence of the original vanishing. -/
lemma restricted_acyclic (A : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat)
    (hA : Acyclic f.base A) :
    Acyclic (f ∣_ U).base ((restriction (f ⁻¹ᵁ U)).obj A) := by
  intro n
  let J := imageResolution (restriction U) (directImageResolution f.base A hA)
  have hz := (HomologicalComplex.exactAt_iff_isZero_homology J.cocomplex (n + 1)).mp
    (J.cocomplex_exactAt_succ n)
  exact hz.of_iso ((sourceResolution f U A).isoRightDerivedObj
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ∣_ U).base) (n + 1) ≪≫
      (HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso (imageComplexIso f U A hA))

/-- Transport the restricted pushed resolution through the underived restriction square. -/
def restrictionImageHom (A : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat)
    (hA : Acyclic f.base A) :
    (imageResolution (restriction U) (directImageResolution f.base A hA)).Hom
      (ofRightDerivedVanishing (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ∣_ U).base)
        (sourceResolution f U A) (restricted_acyclic f U A hA))
      ((pushforwardRestriction f U).hom.app A) where
  hom := (imageComplexIso f U A hA).inv
  ι_f_zero_comp_hom_f_zero := by
    change (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base ⋙ restriction U).map
        ((injectiveResolution A).ι.f 0) ≫ (pushforwardRestriction f U).hom.app _ =
      (pushforwardRestriction f U).hom.app A ≫
        (restriction (f ⁻¹ᵁ U) ⋙
          TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ∣_ U).base).map
            ((injectiveResolution A).ι.f 0)
    exact (pushforwardRestriction f U).hom.naturality _

section Cocycles

local instance sheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) := HasExt.standard _

local instance topSheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} T) := HasExt.standard _

open AbsoluteDirectImageCohomology

/-- Restrict a section cocycle to global sections of the open subspace. -/
def restrictedCycles {S : TopCat.{u}} (W : Opens S)
    {A : TopCat.Sheaf AddCommGrpCat.{u} S} (I : InjectiveResolution A) (n : ℕ) :
    OpenDirectImageCohomology.sectionCycles W I n →+
      sectionCycles (imageResolution (restriction W) I) n where
  toFun x := ⟨(restrictionTopIso W (I.cocomplex.X n)).inv x.1, by
    apply (restrictionTopIso W (I.cocomplex.X (n + 1))).addCommGroupIsoToAddEquiv.injective
    change (restrictionTopIso W (I.cocomplex.X (n + 1))).hom
      (((restriction W).map (I.cocomplex.d n (n + 1))).hom.app (op ⊤) _) = _
    rw [OpenSheafFreeComparison.restrictionTopIso_naturality]
    simpa only [Iso.inv_hom_id_apply, map_zero] using
      (show (I.cocomplex.d n (n + 1)).hom.app (op W) x.1 = 0 from x.2)⟩
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

local instance restrictedHasExt {S : TopCat.{u}} (W : Opens S) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- The Ext open comparison preserves the represented section cocycle. -/
lemma openHEquiv_sectionClass {S : TopCat.{u}} (W : Opens S)
    {A : TopCat.Sheaf AddCommGrpCat.{u} S} (I : InjectiveResolution A) (n : ℕ)
    (x : OpenDirectImageCohomology.sectionCycles W I n) :
    OpenSheafCohomology.openHEquiv.{u, u + 1} W A n
        (OpenDirectImageCohomology.sectionClass W I n x) =
      sectionClass (imageResolution (restriction W) I) n (restrictedCycles W I n x) := by
  change OpenSheafCohomology.openHEquiv.{u, u + 1} W A n
    (I.extMk ((CechFreeOpen.freeOpenHomEquiv W (I.cocomplex.X n)).symm x.1)
      (n + 1) rfl (OpenDirectImageCohomology.sectionHom_d W I n x)) = _
  refine (ExactFunctorInjectiveExt.openHEquiv_extMk W I
    ((CechFreeOpen.freeOpenHomEquiv W (I.cocomplex.X n)).symm x.1)
    (OpenDirectImageCohomology.sectionHom_d W I n x)).trans ?_
  have h : (adjunction W).homEquiv _ _
      ((OpenSheafFreeComparison.extensionFreeOpenIso W).hom ≫
        (CechFreeOpen.freeOpenHomEquiv W (I.cocomplex.X n)).symm x.1) =
      (sectionHomEquiv ((restriction W).obj (I.cocomplex.X n))).symm
        ((restrictionTopIso W (I.cocomplex.X n)).inv x.1) := by
    apply (sectionHomEquiv ((restriction W).obj (I.cocomplex.X n))).injective
    apply (restrictionTopIso W (I.cocomplex.X n)).addCommGroupIsoToAddEquiv.injective
    change (restrictionTopIso W (I.cocomplex.X n)).hom
      (OpenSheafFreeComparison.constantIntegerHomEquiv _ _) = _
    rw [openHEquiv_extMk_section]
    erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    exact ((restrictionTopIso W (I.cocomplex.X n)).addCommGroupIsoToAddEquiv.apply_symm_apply
      x.1).symm
  simp only [sectionClass, AddMonoidHom.coe_mk, h]
  rfl

/-- Restriction of image section cocycles agrees with restriction of source cocycles. -/
lemma restrictionImageHom_cycles (A : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat)
    (hA : Acyclic f.base A) (n : ℕ)
    (x : OpenDirectImageCohomology.sectionCycles (f ⁻¹ᵁ U) (injectiveResolution A) n) :
    sectionCyclesMap (restrictionImageHom f U A hA).hom n
      (restrictedCycles U (directImageResolution f.base A hA) n x) =
        restrictedCycles (f ⁻¹ᵁ U) (injectiveResolution A) n x := by
  ext
  change ((injectiveResolution A).cocomplex.X n).obj.map _
    (((injectiveResolution A).cocomplex.X n).obj.map _ x.1) =
      ((injectiveResolution A).cocomplex.X n).obj.map _ x.1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The absolute comparison computes on any source resolution, not just the chosen one. -/
lemma positiveEquiv_anyResolution {S T : TopCat.{u}} (g : S ⟶ T)
    (A : TopCat.Sheaf AddCommGrpCat.{u} S) (hA : Acyclic g A)
    (I : InjectiveResolution A) (n : ℕ) (x : sectionCycles I (n + 1)) :
    positiveEquiv g A hA n
      (sectionClass (ofRightDerivedVanishing
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g) I hA) (n + 1) x) =
      sectionClass I (n + 1) x := by
  let φ : I.Hom (injectiveResolution A) (𝟙 A) :=
    ⟨InjectiveResolution.desc (𝟙 A) _ I,
      InjectiveResolution.desc_commutes_zero (𝟙 A) _ I⟩
  let ψ : (ofRightDerivedVanishing (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g) I hA).Hom
      (directImageResolution g A hA) (𝟙 _) :=
    { hom := ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).mapHomologicalComplex _).map
        φ.hom
      ι_f_zero_comp_hom_f_zero := by
        change (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map (I.ι.f 0) ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map (φ.hom.f 0) =
          𝟙 _ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).map _
        rw [← Functor.map_comp, φ.ι_f_zero_comp_hom_f_zero]
        simp }
  have hs := sectionClass_naturality φ (n + 1) x
  have ht := sectionClass_naturality ψ (n + 1) x
  erw [Sheaf.H.map_id_apply] at hs ht
  rw [ht, positiveEquiv_sectionClass]
  exact hs.symm

/-- The open comparison agrees with the absolute comparison on the restricted morphism. -/
lemma positiveEquiv_restriction (A : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat)
    (hA : Acyclic f.base A) (n : ℕ)
    (x : Sheaf.H'.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj A)
      (n + 1) U) :
    OpenSheafCohomology.openHEquiv.{u, u + 1} (f ⁻¹ᵁ U) A (n + 1)
      (OpenDirectImageCohomology.positiveEquiv f.base A hA U n x) =
      positiveEquiv (f ∣_ U).base ((restriction (f ⁻¹ᵁ U)).obj A)
        (restricted_acyclic f U A hA) n
        (Sheaf.H.map ((pushforwardRestriction f U).hom.app A) (n + 1)
          (OpenSheafCohomology.openHEquiv.{u, u + 1} U _ (n + 1) x)) := by
  obtain ⟨x, rfl⟩ := OpenDirectImageCohomology.sectionClass_surjective U
    (directImageResolution f.base A hA) (n + 1) x
  refine (congrArg (OpenSheafCohomology.openHEquiv.{u, u + 1}
    (f ⁻¹ᵁ U) A (n + 1))
    (OpenDirectImageCohomology.positiveEquiv_sectionClass f.base A hA U n x)).trans ?_
  refine (openHEquiv_sectionClass (f ⁻¹ᵁ U) (injectiveResolution A) (n + 1) x).trans ?_
  refine (positiveEquiv_anyResolution (f ∣_ U).base _ (restricted_acyclic f U A hA)
    (sourceResolution f U A) n (restrictedCycles (f ⁻¹ᵁ U)
      (injectiveResolution A) (n + 1) x)).symm.trans ?_
  apply congrArg (positiveEquiv (f ∣_ U).base _ (restricted_acyclic f U A hA) n)
  symm
  refine (congrArg (Sheaf.H.map ((pushforwardRestriction f U).hom.app A) (n + 1))
    (openHEquiv_sectionClass U (directImageResolution f.base A hA) (n + 1) x)).trans ?_
  refine (sectionClass_naturality (restrictionImageHom f U A hA) (n + 1)
    (restrictedCycles U (directImageResolution f.base A hA) (n + 1) x)).trans ?_
  exact congrArg (sectionClass _ (n + 1)) (restrictionImageHom_cycles f U A hA (n + 1) x)

/-- Degree-zero open restriction is the usual identification of sections. -/
lemma equivZero_openHEquiv {S : TopCat.{u}} (W : Opens S)
    (A : TopCat.Sheaf AddCommGrpCat.{u} S) (x : Sheaf.H'.{u + 1} A 0 W) :
    Sheaf.H.equiv₀ ((restriction W).obj A) isTerminalTop
      (OpenSheafCohomology.openHEquiv.{u, u + 1} W A 0 x) =
      (restrictionTopIso W A).inv (CechFreeOpen.hPrimeZeroEquiv W A x) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective (CechFreeOpen.freeOpen W) A).2 x
  change Sheaf.H.equiv₀ _ isTerminalTop ((adjunction W).extEquiv
    ((Ext.mk₀ (OpenSheafFreeComparison.extensionFreeOpenIso W).hom).comp
      (Ext.mk₀ a) (zero_add 0))) = _
  rw [Ext.mk₀_comp_mk₀, Adjunction.extEquiv_mk₀]
  change OpenSheafFreeComparison.constantIntegerHomEquiv ((restriction W).obj A)
    (Ext.homEquiv₀ (Ext.homEquiv₀.symm ((adjunction W).homEquiv _ _
      ((OpenSheafFreeComparison.extensionFreeOpenIso W).hom ≫ a)))) = _
  rw [Equiv.apply_symm_apply]
  apply (restrictionTopIso W A).addCommGroupIsoToAddEquiv.injective
  change (restrictionTopIso W A).hom (OpenSheafFreeComparison.constantIntegerHomEquiv _
    ((adjunction W).homEquiv _ _ ((OpenSheafFreeComparison.extensionFreeOpenIso W).hom ≫ a))) = _
  refine (OpenSheafFreeComparison.extensionFreeOpenIso_hom_evaluation W A a).trans ?_
  symm
  refine ((restrictionTopIso W A).addCommGroupIsoToAddEquiv.apply_symm_apply
    (CechFreeOpen.hPrimeZeroEquiv W A (Ext.mk₀ a))).trans ?_
  exact congrArg (CechFreeOpen.freeOpenHomEquiv W A) (Ext.homEquiv₀.apply_symm_apply a)

/-- The underived restriction square identifies the same sections on the inverse image. -/
lemma pushforwardRestriction_top (A : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat)
    (x : A.obj.obj (op (f ⁻¹ᵁ U))) :
    ((pushforwardRestriction f U).hom.app A).hom.app (op ⊤)
      ((restrictionTopIso U ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj A)).inv x) =
      (restrictionTopIso (f ⁻¹ᵁ U) A).inv x := by
  change A.obj.map _ (A.obj.map _ x) = A.obj.map _ x
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction identifies the open and local absolute comparisons in every degree. -/
lemma cohomologyEquiv_restriction (A : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat)
    (hA : Acyclic f.base A) (n : ℕ)
    (x : Sheaf.H'.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj A) n U) :
    OpenSheafCohomology.openHEquiv.{u, u + 1} (f ⁻¹ᵁ U) A n
      (OpenDirectImageCohomology.cohomologyEquiv f.base A hA U n x) =
      cohomologyEquiv (f ∣_ U).base ((restriction (f ⁻¹ᵁ U)).obj A)
        (restricted_acyclic f U A hA) n
        (Sheaf.H.map ((pushforwardRestriction f U).hom.app A) n
          (OpenSheafCohomology.openHEquiv.{u, u + 1} U _ n x)) := by
  cases n with
  | succ n => exact positiveEquiv_restriction f U A hA n x
  | zero =>
    apply (Sheaf.H.equiv₀ ((restriction (f ⁻¹ᵁ U)).obj A) isTerminalTop).injective
    refine (equivZero_openHEquiv (f ⁻¹ᵁ U) A _).trans ?_
    refine (congrArg ((restrictionTopIso (f ⁻¹ᵁ U) A).inv)
      ((CechFreeOpen.hPrimeZeroEquiv (f ⁻¹ᵁ U) A).apply_symm_apply _)).trans ?_
    refine (pushforwardRestriction_top f U A _).symm.trans ?_
    refine (congrArg (((pushforwardRestriction f U).hom.app A).hom.app (op ⊤))
      (equivZero_openHEquiv U _ x).symm).trans ?_
    refine (Sheaf.H.equiv₀_naturality isTerminalTop
      ((pushforwardRestriction f U).hom.app A) _).trans ?_
    exact ((Sheaf.H.equiv₀ ((restriction (f ⁻¹ᵁ U)).obj A) isTerminalTop).apply_symm_apply
      _).symm

/-- The actual absolute comparison on the restricted morphism, with internal local acyclicity. -/
def localComparison (A : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat)
    (hA : Acyclic f.base A) (n : ℕ)
    (x : Sheaf.H'.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj A) n U) :
    Sheaf.H.{u + 1} ((restriction (f ⁻¹ᵁ U)).obj A) n :=
  cohomologyEquiv (f ∣_ U).base _ (restricted_acyclic f U A hA) n
    (Sheaf.H.map ((pushforwardRestriction f U).hom.app A) n
      (OpenSheafCohomology.openHEquiv.{u, u + 1} U _ n x))

lemma localComparison_eq (A : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat)
    (hA : Acyclic f.base A) (n : ℕ)
    (x : Sheaf.H'.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj A) n U) :
    localComparison f U A hA n x = OpenSheafCohomology.openHEquiv.{u, u + 1} (f ⁻¹ᵁ U) A n
      (OpenDirectImageCohomology.cohomologyEquiv f.base A hA U n x) :=
  (cohomologyEquiv_restriction f U A hA n x).symm

/-- The restricted absolute comparisons commute with coefficient maps in every degree. -/
lemma localComparison_naturality {A B : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat}
    (α : A ⟶ B) (hA : Acyclic f.base A) (hB : Acyclic f.base B) (n : ℕ)
    (x : Sheaf.H'.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj A) n U) :
    localComparison f U B hB n
      (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Y) n).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).map α)).app (op U) x) =
      Sheaf.H.map ((restriction (f ⁻¹ᵁ U)).map α) n (localComparison f U A hA n x) := by
  refine (localComparison_eq f U B hB n _).trans ?_
  refine (congrArg (OpenSheafCohomology.openHEquiv.{u, u + 1} (f ⁻¹ᵁ U) B n)
    (OpenDirectImageCohomology.cohomologyEquiv_naturality f.base α hA hB U n x)).trans ?_
  refine (OpenSheafCohomology.openHEquiv_naturality (f ⁻¹ᵁ U) α n _).trans ?_
  exact congrArg (Sheaf.H.map ((restriction (f ⁻¹ᵁ U)).map α) n)
    (localComparison_eq f U A hA n x).symm

/-- The restricted absolute comparisons commute with inclusions of opens in every degree. -/
lemma localComparison_restrict (A : TopCat.Sheaf AddCommGrpCat.{u} X.toTopCat)
    (hA : Acyclic f.base A) {V : Y.Opens} (i : V ⟶ U) (n : ℕ)
    (x : Sheaf.H'.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj A) n U) :
    localComparison f V A hA n
      ((((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).obj A).cohomologyPresheaf n).map
        i.op x) =
      OpenSheafCohomology.openHEquiv.{u, u + 1} (f ⁻¹ᵁ V) A n
        ((A.cohomologyPresheaf n).map ((Opens.map f.base).map i).op
          ((OpenSheafCohomology.openHEquiv.{u, u + 1} (f ⁻¹ᵁ U) A n).symm
            (localComparison f U A hA n x))) := by
  refine (localComparison_eq f V A hA n _).trans ?_
  refine (congrArg (OpenSheafCohomology.openHEquiv.{u, u + 1} (f ⁻¹ᵁ V) A n)
    (OpenDirectImageNaturality.cohomologyEquiv_restrict f.base A hA i n x)).trans ?_
  apply congrArg (OpenSheafCohomology.openHEquiv.{u, u + 1} (f ⁻¹ᵁ V) A n)
  apply congrArg ((A.cohomologyPresheaf n).map ((Opens.map f.base).map i).op)
  exact ((congrArg (OpenSheafCohomology.openHEquiv.{u, u + 1} (f ⁻¹ᵁ U) A n).symm
    (localComparison_eq f U A hA n x)).trans
      ((OpenSheafCohomology.openHEquiv.{u, u + 1} (f ⁻¹ᵁ U) A n).symm_apply_apply _)).symm

end Cocycles

end FLT.Mazur.OpenDirectImageRestriction

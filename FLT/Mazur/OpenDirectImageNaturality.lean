/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenDirectImageCohomology
public import FLT.Mazur.AffineCohomologyVanishingLocal

/-!
# Restriction naturality of acyclic direct-image comparison

The cocycle comparison commutes with inclusions of opens. On the whole space
it is the absolute comparison, so its square with restriction of global
cohomology commutes as well. The open comparisons form a natural presheaf
isomorphism, including degree zero.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Abelian

universe u

namespace FLT.Mazur.OpenDirectImageNaturality

open CechFreeOpen CechFreeResolution OpenDirectImageCohomology
open AffineCohomologyVanishingLocal AcyclicDirectImageResolution
open AbsoluteDirectImageCohomology (Acyclic)

local instance sheafHasExt (X : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := HasExt.standard _

local instance topSheafHasExt (X : TopCat.{u}) :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) := HasExt.standard _

variable {X : TopCat.{u}}

/-- Restriction of sections preserves resolution cocycles. -/
def sectionCyclesRestrict {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) {V U : Opens X} (i : V ⟶ U) (n : ℕ) :
    sectionCycles U I n →+ sectionCycles V I n where
  toFun x := ⟨(I.cocomplex.X n).obj.map i.op x.1, by
    change (I.cocomplex.d n (n + 1)).hom.app (op V) _ = 0
    have h := ConcreteCategory.congr_hom ((I.cocomplex.d n (n + 1)).hom.naturality i.op) x.1
    exact h.trans ((congrArg (fun y ↦ (I.cocomplex.X (n + 1)).obj.map i.op y) x.2).trans
      (map_zero _))⟩
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

/-- The cocycle presentation commutes with restriction of opens in every degree. -/
lemma sectionClass_restrict {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) {V U : Opens X} (i : V ⟶ U) (n : ℕ)
    (x : sectionCycles U I n) :
    (F.cohomologyPresheaf n).map i.op (sectionClass U I n x) =
      sectionClass V I n (sectionCyclesRestrict I i n x) := by
  rw [restriction_eq]
  change (Ext.mk₀ (freeOpenMap i)).comp
    (I.extMk _ _ rfl (sectionHom_d U I n x)) (zero_add n) = _
  rw [InjectiveResolution.mk₀_comp_extMk]
  have h : freeOpenMap i ≫ (freeOpenHomEquiv U (I.cocomplex.X n)).symm x.1 =
      (freeOpenHomEquiv V (I.cocomplex.X n)).symm
        ((I.cocomplex.X n).obj.map i.op x.1) := by
    apply (freeOpenHomEquiv V _).injective
    simp only [freeOpenHomEquiv_naturality_open, AddEquiv.apply_symm_apply]
  simp only [sectionClass, AddMonoidHom.coe_mk, h]
  rfl

/-- The top free-open augmentation identifies the two section evaluations. -/
lemma freeOpenHomEquiv_top_augmentation (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (a : AbsoluteDirectImageCohomology.integers X ⟶ F) :
    freeOpenHomEquiv ⊤ F (freeOpenAugmentation (⊤ : Opens X) ≫ a) =
      AbsoluteDirectImageCohomology.sectionHomEquiv F a := by
  rw [freeOpenHomEquiv_naturality]
  change a.hom.app (op ⊤)
    ((freeOpenAugmentation (⊤ : Opens X)).hom.app (op ⊤) (freeOpenGenerator ⊤ ⊤ (𝟙 _))) = _
  rw [freeOpenAugmentation_generator]
  rfl

/-- On cocycles the top-open equivalence preserves the represented section. -/
lemma sheafHTopEquiv_sectionClass {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ)
    (x : AbsoluteDirectImageCohomology.sectionCycles I n) :
    sheafHTopEquiv F n (AbsoluteDirectImageCohomology.sectionClass I n x) =
      sectionClass ⊤ I n x := by
  change (Ext.mk₀ (freeOpenAugmentation (⊤ : Opens X))).comp
    (I.extMk _ _ rfl (AbsoluteDirectImageCohomology.sectionHom_d I n x)) (zero_add n) = _
  rw [InjectiveResolution.mk₀_comp_extMk]
  have h : freeOpenAugmentation (⊤ : Opens X) ≫
      (AbsoluteDirectImageCohomology.sectionHomEquiv (I.cocomplex.X n)).symm x.1 =
      (freeOpenHomEquiv ⊤ (I.cocomplex.X n)).symm x.1 := by
    apply (freeOpenHomEquiv (⊤ : Opens X) (I.cocomplex.X n)).injective
    simp only [freeOpenHomEquiv_top_augmentation, AddEquiv.apply_symm_apply]
  simp only [sectionClass, AddMonoidHom.coe_mk, h]
  rfl

/-- In degree zero the top-open equivalence preserves global sections. -/
lemma hPrimeZeroEquiv_sheafHTopEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (x : Sheaf.H.{u + 1} F 0) :
    hPrimeZeroEquiv ⊤ F (sheafHTopEquiv F 0 x) = Sheaf.H.equiv₀ F isTerminalTop x := by
  obtain ⟨a, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  change freeOpenHomEquiv ⊤ F (Ext.addEquiv₀
    ((Ext.mk₀ (freeOpenAugmentation (⊤ : Opens X))).comp (Ext.mk₀ a) (zero_add 0))) = _
  rw [Ext.mk₀_comp_mk₀]
  change freeOpenHomEquiv ⊤ F (Ext.addEquiv₀ (Ext.addEquiv₀.symm
    (freeOpenAugmentation (⊤ : Opens X) ≫ a))) =
      AbsoluteDirectImageCohomology.sectionHomEquiv F (Ext.addEquiv₀ (Ext.addEquiv₀.symm a))
  simp only [AddEquiv.apply_symm_apply, freeOpenHomEquiv_top_augmentation]

variable {Y : TopCat.{u}} (f : X ⟶ Y)

/-- Acyclic direct-image comparison commutes with every inclusion of opens. -/
lemma cohomologyEquiv_restrict (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : Acyclic f F) {V U : Opens Y} (i : V ⟶ U) (n : ℕ)
    (x : Sheaf.H'.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n U) :
    cohomologyEquiv f F hF V n
        ((((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F).cohomologyPresheaf n).map
          i.op x) =
      (F.cohomologyPresheaf n).map ((Opens.map f).map i).op
        (cohomologyEquiv f F hF U n x) := by
  cases n with
  | zero =>
    apply (hPrimeZeroEquiv _ F).injective
    change hPrimeZeroEquiv _ F ((hPrimeZeroEquiv _ F).symm _) = _
    rw [AddEquiv.apply_symm_apply, hPrimeZeroEquiv_restrict]
    change _ = F.obj.map _ ((hPrimeZeroEquiv _ F) ((hPrimeZeroEquiv _ F).symm _))
    rw [AddEquiv.apply_symm_apply]
    exact hPrimeZeroEquiv_restrict ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) i x
  | succ n =>
    obtain ⟨x, rfl⟩ := sectionClass_surjective U (directImageResolution f F hF) (n + 1) x
    change positiveEquiv f F hF V n _ = _
    rw [sectionClass_restrict, positiveEquiv_sectionClass]
    change _ = (F.cohomologyPresheaf (n + 1)).map _
      (positiveEquiv f F hF U n _)
    rw [positiveEquiv_sectionClass, sectionClass_restrict]
    rfl

/-- On the whole space the open comparison agrees with the absolute comparison. -/
lemma cohomologyEquiv_top (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : Acyclic f F) (n : ℕ)
    (x : Sheaf.H.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n) :
    cohomologyEquiv f F hF ⊤ n
        (sheafHTopEquiv ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n x) =
      sheafHTopEquiv F n (AbsoluteDirectImageCohomology.cohomologyEquiv f F hF n x) := by
  cases n with
  | zero =>
    apply (hPrimeZeroEquiv ⊤ F).injective
    change hPrimeZeroEquiv ⊤ F ((hPrimeZeroEquiv ⊤ F).symm _) = _
    rw [AddEquiv.apply_symm_apply]
    exact (hPrimeZeroEquiv_sheafHTopEquiv
      ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) x).trans
        (((Sheaf.H.equiv₀ F isTerminalTop).apply_symm_apply _).symm.trans
          (hPrimeZeroEquiv_sheafHTopEquiv F _).symm)
  | succ n =>
    obtain ⟨x, rfl⟩ := AbsoluteDirectImageCohomology.sectionClass_surjective
      (directImageResolution f F hF) (n + 1) x
    change positiveEquiv f F hF ⊤ n _ = sheafHTopEquiv F (n + 1)
      (AbsoluteDirectImageCohomology.positiveEquiv f F hF n _)
    rw [sheafHTopEquiv_sectionClass, positiveEquiv_sectionClass,
      AbsoluteDirectImageCohomology.positiveEquiv_sectionClass, sheafHTopEquiv_sectionClass]
    rfl

/-- Restriction of absolute classes commutes with the open direct-image comparison. -/
lemma cohomologyEquiv_restrictSheafH (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : Acyclic f F) (U : Opens Y) (n : ℕ)
    (x : Sheaf.H.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n) :
    cohomologyEquiv f F hF U n
        (restrictSheafH ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n U x) =
      restrictSheafH F n ((Opens.map f).obj U)
        (AbsoluteDirectImageCohomology.cohomologyEquiv f F hF n x) := by
  rw [← restrictSheafH_naturality _ n (homOfLE le_top) x, restrictSheafH_top,
    cohomologyEquiv_restrict, cohomologyEquiv_top]
  exact restrictSheafH_naturality F n ((Opens.map f).map (homOfLE le_top)) _

/-- The open comparisons give an isomorphism of cohomology presheaves. -/
def cohomologyPresheafIso (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : Acyclic f F) (n : ℕ) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F).cohomologyPresheaf n ≅
      (Opens.map f).op ⋙ F.cohomologyPresheaf n :=
  NatIso.ofComponents (fun U ↦ (cohomologyEquiv f F hF U.unop n).toAddCommGrpIso)
    (fun i ↦ by ext x; exact cohomologyEquiv_restrict f F hF i.unop n x)

/-- The presheaf isomorphism is natural in acyclic coefficients. -/
lemma cohomologyPresheafIso_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (α : F ⟶ G) (hF : Acyclic f F) (hG : Acyclic f G) (n : ℕ) :
    (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Y) n).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat f).map α) ≫
      (cohomologyPresheafIso f G hG n).hom =
    (cohomologyPresheafIso f F hF n).hom ≫
      Functor.whiskerLeft (Opens.map f).op
        ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map α) := by
  ext U x
  exact cohomologyEquiv_naturality f α hF hG U.unop n x

end FLT.Mazur.OpenDirectImageNaturality

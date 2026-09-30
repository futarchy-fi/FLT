/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AbsoluteDirectImageCohomology
public import FLT.Mazur.CechFreeOpen

/-!
# Open cohomology of an acyclic direct image

Sections of the chosen source resolution and its direct image give the same
cocycle presentation on corresponding opens. This constructs the comparison
from vanishing of the actual positive direct images, naturally in coefficients.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Abelian

universe u

namespace FLT.Mazur.OpenDirectImageCohomology

open CechFreeOpen AcyclicDirectImageResolution
open AbsoluteDirectImageCohomology (Acyclic presentationEquiv presentationEquiv_apply
  sourceLift imageLift)

local instance sheafHasExt (X : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := HasExt.standard _

local instance topSheafHasExt (X : TopCat.{u}) :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) := HasExt.standard _

variable {X : TopCat.{u}} (U : Opens X)

lemma sectionHomEquiv_comp {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (a : freeOpen U ⟶ F) (b : F ⟶ G) :
    freeOpenHomEquiv U G (a ≫ b) = b.hom.app (op U) (freeOpenHomEquiv U F a) :=
  freeOpenHomEquiv_naturality b U a

lemma sectionHomEquiv_symm_comp {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (a : F.obj.obj (op U)) (b : F ⟶ G) :
    (freeOpenHomEquiv U F).symm a ≫ b =
      (freeOpenHomEquiv U G).symm (b.hom.app (op U) a) := by
  apply (freeOpenHomEquiv U G).injective
  simp [sectionHomEquiv_comp]

/-- Section cocycles of an injective resolution. -/
def sectionCycles {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) : AddSubgroup ((I.cocomplex.X n).obj.obj (op U)) :=
  ((I.cocomplex.d n (n + 1)).hom.app (op U)).hom.ker

/-- A section cocycle corresponds to a morphism killed by the differential. -/
lemma sectionHom_d {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) (x : sectionCycles U I n) :
    (freeOpenHomEquiv U (I.cocomplex.X n)).symm x.1 ≫ I.cocomplex.d n (n + 1) = 0 := by
  rw [sectionHomEquiv_symm_comp, show
    (I.cocomplex.d n (n + 1)).hom.app (op U) x.1 = 0 from x.2, map_zero]

/-- A section cocycle gives an actual Ext class. -/
def sectionClass {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) : sectionCycles U I n →+ Sheaf.H'.{u + 1} F n U where
  toFun x := InjectiveResolution.extMk.{u + 1} I
    ((freeOpenHomEquiv U (I.cocomplex.X n)).symm x.1) (n + 1) rfl (sectionHom_d U I n x)
  map_zero' := by simp
  map_add' x y := by
    have hx : (freeOpenHomEquiv U (I.cocomplex.X n)).symm x.1 ≫
        I.cocomplex.d n (n + 1) = 0 := by
      rw [sectionHomEquiv_symm_comp, show
        (I.cocomplex.d n (n + 1)).hom.app (op U) x.1 = 0 from x.2, map_zero]
    have hy : (freeOpenHomEquiv U (I.cocomplex.X n)).symm y.1 ≫
        I.cocomplex.d n (n + 1) = 0 := by
      rw [sectionHomEquiv_symm_comp, show
        (I.cocomplex.d n (n + 1)).hom.app (op U) y.1 = 0 from y.2, map_zero]
    simpa only [AddSubgroup.coe_add, map_add] using
      (InjectiveResolution.add_extMk.{u + 1} I _ _ (n + 1) rfl hx hy).symm

/-- Every Ext class is represented by a section cocycle. -/
lemma sectionClass_surjective {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) : Function.Surjective (sectionClass U I n) := by
  intro x
  obtain ⟨a, ha, rfl⟩ := InjectiveResolution.extMk_surjective.{u + 1} I x (n + 1) rfl
  refine ⟨⟨freeOpenHomEquiv U _ a, ?_⟩, ?_⟩
  · change (I.cocomplex.d n (n + 1)).hom.app (op U) _ = 0
    rw [← sectionHomEquiv_comp, ha, map_zero]
  · simp [sectionClass]

/-- In positive degree the kernel consists exactly of section boundaries. -/
lemma sectionClass_eq_zero_iff {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) (x : sectionCycles U I (n + 1)) :
    sectionClass U I (n + 1) x = 0 ↔
      ∃ y : (I.cocomplex.X n).obj.obj (op U),
        (I.cocomplex.d n (n + 1)).hom.app (op U) y = x.1 := by
  change InjectiveResolution.extMk.{u + 1} I _ _ rfl (sectionHom_d U I (n + 1) x) = 0 ↔ _
  rw [InjectiveResolution.extMk_eq_zero_iff.{u + 1} I _ _ _ _ n rfl]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨freeOpenHomEquiv U _ a, by
      rw [← sectionHomEquiv_comp, ha, AddEquiv.apply_symm_apply]⟩
  · rintro ⟨y, hy⟩
    exact ⟨(freeOpenHomEquiv U (I.cocomplex.X n)).symm y, by
      rw [sectionHomEquiv_symm_comp, hy]⟩


/-- Resolution morphisms act on section cocycles degreewise. -/
def sectionCyclesMap {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) : sectionCycles U I n →+ sectionCycles U J n where
  toFun x := ⟨(φ.f n).hom.app (op U) x.1, by
    change (J.cocomplex.d n (n + 1)).hom.app (op U) _ = 0
    have h := congrArg (fun k ↦ k.hom.app (op U) x.1) (φ.comm n (n + 1))
    change (J.cocomplex.d n (n + 1)).hom.app (op U) _ =
      (φ.f (n + 1)).hom.app (op U) _ at h
    exact h.trans ((congrArg (fun y ↦ (φ.f (n + 1)).hom.app (op U) y) x.2).trans
      (map_zero _))⟩
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

/-- The section presentation computes the usual map on Ext. -/
lemma sectionClass_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {I : InjectiveResolution F} {J : InjectiveResolution G} {α : F ⟶ G}
    (φ : I.Hom J α) (n : ℕ) (x : sectionCycles U I n) :
    ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map α).app
        (op U) (sectionClass U I n x) =
      sectionClass U J n (sectionCyclesMap U φ.hom n x) := by
  change (InjectiveResolution.extMk.{u + 1} I _ _ rfl (sectionHom_d U I n x)).comp
    (Ext.mk₀ α) (add_zero n) = _
  rw [InjectiveResolution.extMk_comp_mk₀.{u + 1} _ _ _ _ φ]
  simp only [sectionClass, AddMonoidHom.coe_mk, sectionHomEquiv_symm_comp]
  rfl

variable {Y : TopCat.{u}} (f : X ⟶ Y)

/-- The two presentations have identical section boundaries on corresponding opens. -/
lemma sectionClass_ker (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : Acyclic f F) (U : Opens Y) (n : ℕ) :
    (sectionClass U (directImageResolution f F hF) (n + 1)).ker =
      (sectionClass (Opens.map f |>.obj U) (injectiveResolution F) (n + 1)).ker := by
  ext x
  exact (sectionClass_eq_zero_iff U (directImageResolution f F hF) n x).trans
    (sectionClass_eq_zero_iff _ (injectiveResolution F) n x).symm

/-- Positive cohomology on an open computed by the pushed source resolution. -/
def positiveEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : Acyclic f F)
    (U : Opens Y) (n : ℕ) :
    Sheaf.H'.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) (n + 1) U ≃+
      Sheaf.H'.{u + 1} F (n + 1) ((Opens.map f).obj U) :=
  presentationEquiv (sectionClass U (directImageResolution f F hF) (n + 1))
    (sectionClass _ (injectiveResolution F) (n + 1))
    (sectionClass_surjective _ _ _) (sectionClass_surjective _ _ _)
    (sectionClass_ker f F hF U n)

/-- The comparison sends a pushed section cocycle to the same source section cocycle. -/
lemma positiveEquiv_sectionClass (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : Acyclic f F) (U : Opens Y) (n : ℕ)
    (x : sectionCycles ((Opens.map f).obj U) (injectiveResolution F) (n + 1)) :
    positiveEquiv f F hF U n (sectionClass U (directImageResolution f F hF) (n + 1) x) =
      sectionClass _ (injectiveResolution F) (n + 1) x :=
  presentationEquiv_apply _ _ _ _ _ _

/-- Positive comparison is natural for coefficient maps between acyclic sheaves. -/
lemma positiveEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (α : F ⟶ G) (hF : Acyclic f F) (hG : Acyclic f G) (U : Opens Y) (n : ℕ)
    (x : Sheaf.H'.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) (n + 1) U) :
    positiveEquiv f G hG U n
        (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Y) (n + 1)).map
          ((TopCat.Sheaf.pushforward AddCommGrpCat f).map α)).app (op U) x) =
      ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) (n + 1)).map α).app
        (op ((Opens.map f).obj U)) (positiveEquiv f F hF U n x) := by
  obtain ⟨x, rfl⟩ := sectionClass_surjective U (directImageResolution f F hF) (n + 1) x
  rw [sectionClass_naturality U (imageLift f α hF hG), positiveEquiv_sectionClass,
    positiveEquiv_sectionClass, sectionClass_naturality _ (sourceLift α)]
  rfl

/-- Open cohomology comparison, including the section identification in degree zero. -/
def cohomologyEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : Acyclic f F)
    (U : Opens Y) : (n : ℕ) →
    Sheaf.H'.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n U ≃+
      Sheaf.H'.{u + 1} F n ((Opens.map f).obj U)
  | 0 => (hPrimeZeroEquiv U _).trans (hPrimeZeroEquiv _ F).symm
  | n + 1 => positiveEquiv f F hF U n

/-- The open comparison commutes with coefficient maps in every degree. -/
lemma cohomologyEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (α : F ⟶ G) (hF : Acyclic f F) (hG : Acyclic f G) (U : Opens Y) (n : ℕ)
    (x : Sheaf.H'.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n U) :
    cohomologyEquiv f G hG U n
        (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Y) n).map
          ((TopCat.Sheaf.pushforward AddCommGrpCat f).map α)).app (op U) x) =
      ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map α).app
        (op ((Opens.map f).obj U)) (cohomologyEquiv f F hF U n x) := by
  cases n with
  | zero =>
    apply (hPrimeZeroEquiv _ G).injective
    change hPrimeZeroEquiv _ G ((hPrimeZeroEquiv _ G).symm _) = _
    rw [AddEquiv.apply_symm_apply, hPrimeZeroEquiv_naturality]
    change _ = α.hom.app _ ((hPrimeZeroEquiv _ F) ((hPrimeZeroEquiv _ F).symm _))
    rw [AddEquiv.apply_symm_apply]
    exact hPrimeZeroEquiv_naturality
      ((TopCat.Sheaf.pushforward AddCommGrpCat f).map α) U x
  | succ n => exact positiveEquiv_naturality f α hF hG U n x

end FLT.Mazur.OpenDirectImageCohomology

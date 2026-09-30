/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicDirectImageResolution
public import FLT.Mazur.ModuleCohomology
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Absolute cohomology of an acyclic direct image

Section cocycles in the source and pushed injective resolutions give the same
presentation of positive Ext. The resulting comparison is natural in coefficients.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Abelian

universe u

namespace FLT.Mazur.AbsoluteDirectImageCohomology

local instance sheafHasExt (X : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := HasExt.standard _

local instance topSheafHasExt (X : TopCat.{u}) :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} X) := HasExt.standard _

/-- Two surjective additive maps with the same kernel present equivalent groups. -/
def presentationEquiv {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (p : A →+ B) (q : A →+ C) (hp : Function.Surjective p) (hq : Function.Surjective q)
    (h : p.ker = q.ker) : B ≃+ C :=
  AddEquiv.ofBijective (p.liftOfSurjective hp ⟨q, h.le⟩) (by
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := hp x
      obtain ⟨b, rfl⟩ := hp y
      have hab : q (a - b) = 0 := by simpa using sub_eq_zero.mpr hxy
      have : p (a - b) = 0 := h.ge hab
      exact sub_eq_zero.mp (by simpa using this)
    · intro z
      obtain ⟨a, rfl⟩ := hq z
      exact ⟨p a, by simp⟩)

@[simp]
lemma presentationEquiv_apply {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (p : A →+ B) (q : A →+ C) (hp : Function.Surjective p) (hq : Function.Surjective q)
    (h : p.ker = q.ker) (a : A) : presentationEquiv p q hp hq h (p a) = q a := by
  simp [presentationEquiv]

variable {X : TopCat.{u}}

/-- The constant integer sheaf represents global sections. -/
abbrev integers (X : TopCat.{u}) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))

/-- Morphisms from the integer sheaf are global sections, additively. -/
def sectionHomEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (integers X ⟶ F) ≃+ F.obj.obj (op ⊤) :=
  ((constantSheafAdj _ AddCommGrpCat isTerminalTop).homAddEquiv _ F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv _)

lemma sectionHomEquiv_comp {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (a : integers X ⟶ F) (b : F ⟶ G) :
    sectionHomEquiv G (a ≫ b) = b.hom.app (op ⊤) (sectionHomEquiv F a) := by
  rfl

lemma sectionHomEquiv_symm_comp {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (a : F.obj.obj (op ⊤)) (b : F ⟶ G) :
    (sectionHomEquiv F).symm a ≫ b =
      (sectionHomEquiv G).symm (b.hom.app (op ⊤) a) := by
  apply (sectionHomEquiv G).injective
  simp [sectionHomEquiv_comp]

/-- Section cocycles of an injective resolution. -/
def sectionCycles {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) : AddSubgroup ((I.cocomplex.X n).obj.obj (op ⊤)) :=
  ((I.cocomplex.d n (n + 1)).hom.app (op ⊤)).hom.ker

/-- A section cocycle corresponds to a morphism killed by the differential. -/
lemma sectionHom_d {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) (x : sectionCycles I n) :
    (sectionHomEquiv (I.cocomplex.X n)).symm x.1 ≫ I.cocomplex.d n (n + 1) = 0 := by
  rw [sectionHomEquiv_symm_comp, show
    (I.cocomplex.d n (n + 1)).hom.app (op ⊤) x.1 = 0 from x.2, map_zero]

/-- A section cocycle gives an actual Ext class. -/
def sectionClass {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) : sectionCycles I n →+ Sheaf.H.{u + 1} F n where
  toFun x := InjectiveResolution.extMk.{u + 1} I
    ((sectionHomEquiv (I.cocomplex.X n)).symm x.1) (n + 1) rfl (sectionHom_d I n x)
  map_zero' := by simp
  map_add' x y := by
    have hx : (sectionHomEquiv (I.cocomplex.X n)).symm x.1 ≫
        I.cocomplex.d n (n + 1) = 0 := by
      rw [sectionHomEquiv_symm_comp, show
        (I.cocomplex.d n (n + 1)).hom.app (op ⊤) x.1 = 0 from x.2, map_zero]
    have hy : (sectionHomEquiv (I.cocomplex.X n)).symm y.1 ≫
        I.cocomplex.d n (n + 1) = 0 := by
      rw [sectionHomEquiv_symm_comp, show
        (I.cocomplex.d n (n + 1)).hom.app (op ⊤) y.1 = 0 from y.2, map_zero]
    simpa only [AddSubgroup.coe_add, map_add] using
      (InjectiveResolution.add_extMk.{u + 1} I _ _ (n + 1) rfl hx hy).symm

/-- Every Ext class is represented by a section cocycle. -/
lemma sectionClass_surjective {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) : Function.Surjective (sectionClass I n) := by
  intro x
  obtain ⟨a, ha, rfl⟩ := InjectiveResolution.extMk_surjective.{u + 1} I x (n + 1) rfl
  refine ⟨⟨sectionHomEquiv _ a, ?_⟩, ?_⟩
  · change (I.cocomplex.d n (n + 1)).hom.app (op ⊤) _ = 0
    rw [← sectionHomEquiv_comp, ha, map_zero]
  · simp [sectionClass]

/-- In positive degree the kernel consists exactly of section boundaries. -/
lemma sectionClass_eq_zero_iff {F : TopCat.Sheaf AddCommGrpCat.{u} X}
    (I : InjectiveResolution F) (n : ℕ) (x : sectionCycles I (n + 1)) :
    sectionClass I (n + 1) x = 0 ↔
      ∃ y : (I.cocomplex.X n).obj.obj (op ⊤),
        (I.cocomplex.d n (n + 1)).hom.app (op ⊤) y = x.1 := by
  change InjectiveResolution.extMk.{u + 1} I _ _ rfl (sectionHom_d I (n + 1) x) = 0 ↔ _
  rw [InjectiveResolution.extMk_eq_zero_iff.{u + 1} I _ _ _ _ n rfl]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨sectionHomEquiv _ a, by
      rw [← sectionHomEquiv_comp, ha, AddEquiv.apply_symm_apply]⟩
  · rintro ⟨y, hy⟩
    exact ⟨(sectionHomEquiv (I.cocomplex.X n)).symm y, by
      rw [sectionHomEquiv_symm_comp, hy]⟩


/-- Resolution morphisms act on section cocycles degreewise. -/
def sectionCyclesMap {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) : sectionCycles I n →+ sectionCycles J n where
  toFun x := ⟨(φ.f n).hom.app (op ⊤) x.1, by
    change (J.cocomplex.d n (n + 1)).hom.app (op ⊤) _ = 0
    have h := congrArg (fun k ↦ k.hom.app (op ⊤) x.1) (φ.comm n (n + 1))
    change (J.cocomplex.d n (n + 1)).hom.app (op ⊤) _ =
      (φ.f (n + 1)).hom.app (op ⊤) _ at h
    exact h.trans ((congrArg (fun y ↦ (φ.f (n + 1)).hom.app (op ⊤) y) x.2).trans
      (map_zero _))⟩
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

/-- The section presentation computes the usual map on Ext. -/
lemma sectionClass_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    {I : InjectiveResolution F} {J : InjectiveResolution G} {α : F ⟶ G}
    (φ : I.Hom J α) (n : ℕ) (x : sectionCycles I n) :
    Sheaf.H.map α n (sectionClass I n x) =
      sectionClass J n (sectionCyclesMap φ.hom n x) := by
  change (InjectiveResolution.extMk.{u + 1} I _ _ rfl (sectionHom_d I n x)).comp
    (Ext.mk₀ α) (add_zero n) = _
  rw [InjectiveResolution.extMk_comp_mk₀.{u + 1} _ _ _ _ φ]
  simp only [sectionClass, AddMonoidHom.coe_mk, sectionHomEquiv_symm_comp]
  rfl

variable {Y : TopCat.{u}} (f : X ⟶ Y)

/-- Acyclicity means vanishing of the actual positive abelian direct images. -/
abbrev Acyclic (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ n : ℕ, IsZero
    (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived (n + 1)).obj F)

open AcyclicDirectImageResolution

/-- The pushed resolution and the source resolution have identical section boundaries. -/
lemma sectionClass_ker (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : Acyclic f F) (n : ℕ) :
    (sectionClass (directImageResolution f F hF) (n + 1)).ker =
      (sectionClass (injectiveResolution F) (n + 1)).ker := by
  ext x
  exact (sectionClass_eq_zero_iff (directImageResolution f F hF) n x).trans
    (sectionClass_eq_zero_iff (injectiveResolution F) n x).symm

/-- Positive sheaf cohomology computed through the pushed injective resolution. -/
def positiveEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : Acyclic f F) (n : ℕ) :
    Sheaf.H.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) (n + 1) ≃+
      Sheaf.H.{u + 1} F (n + 1) :=
  presentationEquiv (sectionClass (directImageResolution f F hF) (n + 1))
    (sectionClass (injectiveResolution F) (n + 1))
    (sectionClass_surjective _ _) (sectionClass_surjective _ _) (sectionClass_ker f F hF n)

/-- The comparison takes a pushed section cocycle to the same source section cocycle. -/
lemma positiveEquiv_sectionClass (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : Acyclic f F) (n : ℕ) (x : sectionCycles (injectiveResolution F) (n + 1)) :
    positiveEquiv f F hF n (sectionClass (directImageResolution f F hF) (n + 1) x) =
      sectionClass (injectiveResolution F) (n + 1) x :=
  presentationEquiv_apply _ _ _ _ _ _

/-- Lift a coefficient morphism to the chosen source resolutions. -/
def sourceLift {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (α : F ⟶ G) :
    (injectiveResolution F).Hom (injectiveResolution G) α where
  hom := InjectiveResolution.desc α _ _
  ι_f_zero_comp_hom_f_zero := InjectiveResolution.desc_commutes_zero α _ _

/-- Direct image of the source lift respects the constructed augmentations. -/
def imageLift {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (α : F ⟶ G)
    (hF : Acyclic f F) (hG : Acyclic f G) :
    (directImageResolution f F hF).Hom (directImageResolution f G hG)
      ((TopCat.Sheaf.pushforward AddCommGrpCat f).map α) where
  hom := ((TopCat.Sheaf.pushforward AddCommGrpCat f).mapHomologicalComplex _).map
    (sourceLift α).hom
  ι_f_zero_comp_hom_f_zero := by
    change (TopCat.Sheaf.pushforward AddCommGrpCat f).map _ ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat f).map _ =
      (TopCat.Sheaf.pushforward AddCommGrpCat f).map _ ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat f).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (InjectiveResolution.desc_commutes_zero α _ _)

/-- Positive comparison is natural for every coefficient morphism. -/
lemma positiveEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (α : F ⟶ G) (hF : Acyclic f F) (hG : Acyclic f G) (n : ℕ)
    (x : Sheaf.H.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) (n + 1)) :
    positiveEquiv f G hG n
        (Sheaf.H.map ((TopCat.Sheaf.pushforward AddCommGrpCat f).map α) (n + 1) x) =
      Sheaf.H.map α (n + 1) (positiveEquiv f F hF n x) := by
  obtain ⟨x, rfl⟩ := sectionClass_surjective (directImageResolution f F hF) (n + 1) x
  rw [sectionClass_naturality (imageLift f α hF hG), positiveEquiv_sectionClass,
    positiveEquiv_sectionClass, sectionClass_naturality (sourceLift α)]
  rfl

/-- Absolute additive comparison under vanishing of actual positive direct images. -/
def cohomologyEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : Acyclic f F) :
    (n : ℕ) → Sheaf.H.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n ≃+
      Sheaf.H.{u + 1} F n
  | 0 => DirectImageInjectives.hZeroEquiv f F
  | n + 1 => positiveEquiv f F hF n

/-- The absolute comparison commutes with all coefficient morphisms in every degree. -/
lemma cohomologyEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (α : F ⟶ G) (hF : Acyclic f F) (hG : Acyclic f G) (n : ℕ)
    (x : Sheaf.H.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n) :
    cohomologyEquiv f G hG n
        (Sheaf.H.map ((TopCat.Sheaf.pushforward AddCommGrpCat f).map α) n x) =
      Sheaf.H.map α n (cohomologyEquiv f F hF n x) := by
  cases n with
  | zero => exact DirectImageInjectives.hZeroEquiv_naturality f α x
  | succ n => exact positiveEquiv_naturality f α hF hG n x

/-- In particular, every coefficient endomorphism commutes with the comparison. -/
lemma cohomologyEquiv_endomorphism (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : Acyclic f F) (a : F ⟶ F) (n : ℕ)
    (x : Sheaf.H.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) n) :
    cohomologyEquiv f F hF n
        (Sheaf.H.map ((TopCat.Sheaf.pushforward AddCommGrpCat f).map a) n x) =
      Sheaf.H.map a n (cohomologyEquiv f F hF n x) :=
  cohomologyEquiv_naturality f a hF hF n x

/-- Multiplication on an actual module coefficient commutes with the comparison. -/
lemma cohomologyEquiv_moduleMultiply {S : AlgebraicGeometry.Scheme.{u}}
    {T : TopCat.{u}} (g : S.toTopCat ⟶ T) (M : S.Modules)
    (hM : Acyclic g (FCurve.moduleAbelianSheaf M)) (r : S.presheaf.obj (op ⊤)) (n : ℕ)
    (x : Sheaf.H.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat g).obj
      (FCurve.moduleAbelianSheaf M)) n) :
    cohomologyEquiv g _ hM n
        (Sheaf.H.map ((TopCat.Sheaf.pushforward AddCommGrpCat g).map
          (FCurve.moduleMultiply M r)) n x) =
      Sheaf.H.map (FCurve.moduleMultiply M r) n (cohomologyEquiv g _ hM n x) :=
  cohomologyEquiv_endomorphism g _ hM _ n x

end FLT.Mazur.AbsoluteDirectImageCohomology

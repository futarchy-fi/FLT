/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DirectImageInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Injective resolutions of acyclic direct images

A left exact additive functor preserving injectives sends an injective resolution
of an acyclic object to an injective resolution of its image. Acyclicity here is
vanishing of the actual positive right-derived objects. The augmentation is
constructed by applying the functor to the source augmentation. Its exactness
in degree zero follows from preservation of kernels, while positive exactness
follows from the right-derived computation on the source resolution.

The final construction specializes this to direct image of abelian sheaves,
choosing the source injective resolution internally.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace FLT.Mazur.AcyclicDirectImageResolution

section General

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable (T : C ⥤ D) [T.Additive] {F : C} (I : InjectiveResolution F)

/-- The degreewise image of a source injective resolution. -/
def imageComplex : CochainComplex D ℕ :=
  (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

/-- The image augmentation has zero composite with the first differential. -/
lemma augmentation_comp_d :
    T.map (I.ι.f 0) ≫ (imageComplex T I).d 0 1 = 0 := by
  change T.map (I.ι.f 0) ≫ T.map (I.cocomplex.d 0 1) = 0
  rw [← T.map_comp, I.ι_f_zero_comp_complex_d, T.map_zero]

/-- The augmentation is constructed from the source augmentation in degree zero. -/
def augmentation : (CochainComplex.single₀ D).obj (T.obj F) ⟶ imageComplex T I :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨T.map (I.ι.f 0), augmentation_comp_d T I⟩

@[simp]
lemma augmentation_f_zero : (augmentation T I).f 0 = T.map (I.ι.f 0) := by
  simp [augmentation]

variable [PreservesFiniteLimits T]

/-- Left exactness identifies the image augmentation with the first kernel. -/
def augmentationIsKernel :
    IsLimit (KernelFork.ofι (T.map (I.ι.f 0)) (augmentation_comp_d T I)) :=
  KernelFork.mapIsLimit _ I.isLimitKernelFork T

/-- The augmented image complex is exact in degree zero. -/
lemma image_exact_zero :
    (ShortComplex.mk _ _ (augmentation_comp_d T I)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (augmentationIsKernel T I)

variable [HasInjectiveResolutions C]

omit [PreservesFiniteLimits T] in
/-- Positive derived-object vanishing gives positive exactness of the image complex. -/
lemma image_exact_succ
    (hF : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj F)) (n : ℕ) :
    (imageComplex T I).ExactAt (n + 1) := by
  rw [exactAt_iff_isZero_homology]
  exact (hF n).of_iso (I.isoRightDerivedObj T (n + 1)).symm

/-- The constructed augmentation is a quasi-isomorphism for an acyclic object. -/
lemma augmentation_quasiIso
    (hF : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj F)) :
    QuasiIso (augmentation T I) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
    · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
        ⟨image_exact_zero T I, inferInstance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp [augmentation]) (by simp [imageComplex])
    all_goals simp
  | succ n =>
    rw [quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ _)]
    exact image_exact_succ T I hF n

/-- Push a source resolution through a left exact functor preserving injectives. -/
def ofRightDerivedVanishing [T.PreservesInjectiveObjects]
    (hF : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj F)) :
    InjectiveResolution (T.obj F) where
  cocomplex := imageComplex T I
  injective n := T.injective_obj_of_injective (I.injective n)
  ι := augmentation T I
  quasiIso := augmentation_quasiIso T I hF

end General

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X)

/-- Direct image of the chosen source resolution resolves an acyclic direct image. -/
def directImageResolution
    (hF : ∀ n : ℕ, IsZero
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived (n + 1)).obj F)) :
    InjectiveResolution ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) :=
  ofRightDerivedVanishing (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
    (injectiveResolution F) hF

/-- Every term is the direct image of the corresponding source injective. -/
@[simp]
lemma directImageResolution_X
    (hF : ∀ n : ℕ, IsZero
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived (n + 1)).obj F)) (n : ℕ) :
    (directImageResolution f F hF).cocomplex.X n =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj
        ((injectiveResolution F).cocomplex.X n) := rfl

/-- The differentials are obtained by direct image of the source differentials. -/
@[simp]
lemma directImageResolution_d
    (hF : ∀ n : ℕ, IsZero
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived (n + 1)).obj F)) (i j : ℕ) :
    (directImageResolution f F hF).cocomplex.d i j =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map
        ((injectiveResolution F).cocomplex.d i j) := rfl

/-- The augmentation is precisely the direct image of the source augmentation. -/
@[simp]
lemma directImageResolution_ι_zero
    (hF : ∀ n : ℕ, IsZero
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).rightDerived (n + 1)).obj F)) :
    (directImageResolution f F hF).ι.f 0 =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map ((injectiveResolution F).ι.f 0) :=
  augmentation_f_zero _ _

end FLT.Mazur.AcyclicDirectImageResolution

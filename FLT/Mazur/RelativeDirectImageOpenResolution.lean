/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDirectImageComposition

/-!
# The open comparison on the pushed injective resolution

The sheafified open comparison computes on the common image complex, including
in degree zero, where the cocycle identification comes from the augmentation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Abelian HomologicalComplex

universe u

namespace FLT.Mazur.RelativeDirectImageOpenResolution

open HigherDirectImagePresheaf HigherDirectImageOpenSheafification
open OpenDirectImageCohomology AcyclicDirectImageResolution
open RelativeDirectImageComposition CechFreeOpen
open AbsoluteDirectImageCohomology (Acyclic)

local instance sheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) := HasExt.standard _

local instance topSheafHasExt (T : TopCat.{u}) :
    HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u} T) := HasExt.standard _

open CategoryTheory.Localization CochainComplex.HomComplex ExactFunctorInjectiveExt

private lemma extMk_augmentation {C : Type u} [Category C] [Abelian C] [HasExt C]
    {A F : C} (I : InjectiveResolution F) (a : A ⟶ F) :
    I.extMk (a ≫ I.ι.f 0) 1 rfl (by simp) = Ext.mk₀ a := by
  apply (SmallShiftedHom.postcompEquiv I.ι'
    (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)).injective
  rw [show (SmallShiftedHom.postcompEquiv I.ι' _)
    (I.extMk (a ≫ I.ι.f 0) 1 rfl (by simp)) = _ from extMk_postcomp I _ _]
  change SmallShiftedHom.mk _ _ = _
  apply (SmallShiftedHom.equiv _ (HomologicalComplex.quasiIso C (.up ℤ)).Q).injective
  simp only [SmallShiftedHom.postcompEquiv_apply, SmallShiftedHom.equiv_comp,
    Ext.mk₀, SmallShiftedHom.equiv_mk₀, SmallShiftedHom.equiv_mk,
    ShiftedHom.mk₀_comp_mk₀, ← Functor.map_comp]
  have h : cocycleHom I (a ≫ I.ι.f 0) (by simp) =
      ShiftedHom.mk₀ (0 : ℤ) rfl ((CochainComplex.singleFunctor C 0).map a ≫ I.ι') := by
    apply HomologicalComplex.from_single_hom_ext
    simp [cocycleHom, Cocycle.equivHomShift_symm_apply, Cochain.rightShift_v,
      ShiftedHom.mk₀, InjectiveResolution.ι'_f_zero, shiftFunctorZero',
      CochainComplex.shiftFunctorZero_inv_app_f, CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self]
  rw [h]
  exact ShiftedHom.map_mk₀ _ _ _ _

/-- The degree-zero section represented by a cocycle lifts it through the augmentation. -/
lemma hPrimeZeroEquiv_sectionClass {X : TopCat.{u}}
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F)
    (U : Opens X) (x : sectionCycles U I 0) :
    (I.ι.f 0).hom.app (op U) (hPrimeZeroEquiv U F (sectionClass U I 0 x)) = x.1 := by
  let a := (freeOpenHomEquiv U (I.cocomplex.X 0)).symm x.1
  let b := I.isLimitKernelFork.lift (KernelFork.ofι a (sectionHom_d U I 0 x))
  have hb : b ≫ I.ι.f 0 = a :=
    I.isLimitKernelFork.fac (KernelFork.ofι a (sectionHom_d U I 0 x))
      WalkingParallelPair.zero
  change (I.ι.f 0).hom.app (op U)
    (hPrimeZeroEquiv U F (I.extMk a 1 rfl (sectionHom_d U I 0 x))) = _
  have he : I.extMk a 1 rfl (sectionHom_d U I 0 x) = Ext.mk₀ b := by
    simpa only [hb] using extMk_augmentation I b
  rw [he]
  change (I.ι.f 0).hom.app (op U)
    (freeOpenHomEquiv U F (Ext.addEquiv₀.{u + 1} (Ext.addEquiv₀.{u + 1}.symm b))) = _
  rw [AddEquiv.apply_symm_apply]
  exact (sectionHomEquiv_comp U b (I.ι.f 0)).symm.trans
    ((congrArg (freeOpenHomEquiv U (I.cocomplex.X 0)) hb).trans
      ((freeOpenHomEquiv U (I.cocomplex.X 0)).apply_symm_apply _))

variable {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : Acyclic f F)

/-- The original open comparison preserves the represented cocycle in every degree. -/
lemma cohomologyEquiv_sectionClass (U : Opens Y) (n : ℕ)
    (x : sectionCycles ((Opens.map f).obj U) (injectiveResolution F) n) :
    cohomologyEquiv f F hF U n (sectionClass U (directImageResolution f F hF) n x) =
      sectionClass _ (injectiveResolution F) n x := by
  cases n with
  | succ n => exact positiveEquiv_sectionClass f F hF U n x
  | zero =>
    apply (hPrimeZeroEquiv _ F).injective
    change hPrimeZeroEquiv _ F ((hPrimeZeroEquiv _ F).symm _) = _
    rw [AddEquiv.apply_symm_apply]
    apply (AddCommGrpCat.mono_iff_injective
      (((injectiveResolution F).ι.f 0).hom.app (op ((Opens.map f).obj U)))).mp inferInstance
    exact (hPrimeZeroEquiv_sectionClass (directImageResolution f F hF) U x).trans
      (hPrimeZeroEquiv_sectionClass (injectiveResolution F) _ x).symm

/-- The small open comparison is the identity on the common homology presentation. -/
lemma presheafIso_resolution (n : ℕ) :
    (openPresheafIso g (directImageResolution f F hF) n).hom ≫
        (presheafIso f g F hF n).hom =
      (openPresheafIso (f ≫ g) (injectiveResolution F) n).hom := by
  ext U x
  obtain ⟨x, rfl⟩ := homologyClass_surjective g (directImageResolution f F hF) U.unop n x
  apply (openValueEquiv (f ≫ g) F U.unop n).injective
  change openValueEquiv (f ≫ g) F U.unop n
    (valueEquiv f g F hF U.unop n
      ((openValueEquiv g _ U.unop n).symm
        (openEquiv g (directImageResolution f F hF) U.unop n
          (homologyClass g (directImageResolution f F hF) U.unop n x)))) = _
  rw [valueEquiv_decode, AddEquiv.apply_symm_apply, openEquiv_homologyClass,
    cohomologyEquiv_sectionClass]
  exact (openEquiv_homologyClass (f ≫ g) (injectiveResolution F) U.unop n x).symm.trans
    ((openValueEquiv (f ≫ g) F U.unop n).apply_symm_apply _).symm

/-- Changing the injective resolution leaves the open comparison unchanged. -/
lemma openComparison_eq {V W : TopCat.{u}} (p : V ⟶ W)
    {A : TopCat.Sheaf AddCommGrpCat.{u} V} (I J : InjectiveResolution A) (n : ℕ) :
    (openComparison p I n).hom = (openComparison p J n).hom := by
  let φ : I.Hom J (𝟙 A) :=
    ⟨InjectiveResolution.desc (𝟙 A) J I, InjectiveResolution.desc_commutes_zero _ _ _⟩
  have h := openComparison_naturality p φ n
  have hi : openPresheafMap p (𝟙 A) n = 𝟙 _ := by
    ext U x
    simp [openPresheafMap]
    rfl
  rw [hi, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] at h
  exact h.symm

/-- The sheafified comparison computes on the pushed source injective resolution. -/
lemma abelianIso_eq (n : ℕ) :
    (abelianIso f g F hF n).hom =
      ((directImageResolution f F hF).isoRightDerivedObj (directImage g) n).hom ≫
        ((injectiveResolution F).isoRightDerivedObj (directImage (f ≫ g)) n).inv := by
  rw [← cancel_mono (openComparison (f ≫ g) (injectiveResolution F) n).hom]
  simp only [abelianIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [openComparison_eq g (injectiveResolution ((directImage f).obj F))
    (directImageResolution f F hF) n]
  simp only [openComparison, comparison, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
    presheafIso_resolution]
  rfl

end FLT.Mazur.RelativeDirectImageOpenResolution

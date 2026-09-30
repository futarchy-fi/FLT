/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDirectImageOpenResolution

/-!
# Forgetting relative direct-image composition

The actual module comparison forgets to the sheafified open comparison.
The proof compares the two computations using a map from the underlying
module resolution to the chosen abelian injective resolution.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxSynthPendingDepth 1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex

universe u

namespace FLT.Mazur.RelativeDirectImageForgetting

open FCurve CoherentDevissage RelativeDirectImageComposition
open AcyclicResolutionComparison ModuleDerivedAbelianComparison
open HigherDirectImagePresheaf AcyclicDirectImageResolution

variable {S T B : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ B)
  (M : S.Modules) (hM : ModulePushforwardAcyclic f M)

/-- Compare the underlying module resolution with the chosen abelian resolution. -/
def sourceComparison : (underlyingResolution M).cocomplex ⟶
    (injectiveResolution (moduleAbelianSheaf M)).cocomplex :=
  ExactResolution.desc (𝟙 _) (injectiveResolution _) (underlyingResolution M)

/-- The source comparison respects the augmentation. -/
lemma sourceComparison_comm :
    (underlyingResolution M).ι ≫ sourceComparison M =
      (injectiveResolution (moduleAbelianSheaf M)).ι := by
  simp [sourceComparison]

/-- Push the same comparison to the intermediate space. -/
def imageComparison : (forgottenResolution f M hM).cocomplex ⟶
    (directImageResolution f.base (moduleAbelianSheaf M)
      (modulePushforwardAcyclic_abelian f M hM)).cocomplex :=
  ((directImage f.base).mapHomologicalComplex _).map (sourceComparison M)

/-- The pushed comparison also respects the augmentation. -/
lemma imageComparison_comm :
    (forgottenResolution f M hM).ι ≫ imageComparison f M hM =
      (directImageResolution f.base (moduleAbelianSheaf M)
        (modulePushforwardAcyclic_abelian f M hM)).ι := by
  apply HomologicalComplex.from_single_hom_ext
  have h : (moduleToSheaf S).map ((injectiveResolution M).ι.f 0) ≫
      (sourceComparison M).f 0 = (injectiveResolution (moduleAbelianSheaf M)).ι.f 0 := by
    simpa [underlyingResolution, HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
      using congrArg (fun k ↦ k.f 0) (sourceComparison_comm M)
  change (directImage f.base).map ((moduleToSheaf S).map ((injectiveResolution M).ι.f 0)) ≫
    (directImage f.base).map ((sourceComparison M).f 0) =
      (directImage f.base).map ((injectiveResolution (moduleAbelianSheaf M)).ι.f 0)
  rw [← Functor.map_comp, h]

set_option maxHeartbeats 800000 in
-- Elaboration identifies nested direct images and their chosen resolution computations.
/-- The abelian comparison intertwines the two canonical exact-resolution maps. -/
lemma toRightDerived_abelianIso (n : ℕ) :
    (forgottenResolution f M hM).toRightDerived (abelianPushforward g) n ≫
      (abelianIso f.base g.base (moduleAbelianSheaf M)
        (modulePushforwardAcyclic_abelian f M hM) n).hom =
    (underlyingResolution M).toRightDerived (abelianPushforward (f ≫ g)) n := by
  rw [RelativeDirectImageOpenResolution.abelianIso_eq,
    (forgottenResolution f M hM).toRightDerived_eq (abelianPushforward g)
      _ (imageComparison f M hM) (imageComparison_comm f M hM),
    (underlyingResolution M).toRightDerived_eq (abelianPushforward (f ≫ g))
      _ (sourceComparison M) (sourceComparison_comm M)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hc : ((abelianPushforward g).mapHomologicalComplex _).map
      (imageComparison f M hM) =
      ((abelianPushforward (f ≫ g)).mapHomologicalComplex _).map (sourceComparison M) := by
    ext n
    rfl
  dsimp only [ExactResolution.imageHomology, Functor.comp_map, homologyFunctor_map]
  rw [hc]
  rfl

/-- Module pushforward composition is the identity on the underlying image complex. -/
lemma moduleComplexIso_forget :
    ((moduleToSheaf B).mapHomologicalComplex _).map (moduleComplexIso f g M hM).hom =
      𝟙 (((abelianPushforward (f ≫ g)).mapHomologicalComplex _).obj
        (underlyingResolution M).cocomplex) := by
  ext n
  rfl

set_option maxHeartbeats 800000 in
-- Elaboration compares module homology and the homology of the underlying sheaf complex.
/-- Forgetting the homology comparison agrees with exact forgetting on the common complex. -/
lemma moduleComplexHomology_forget (n : ℕ) :
    (moduleToSheaf B).map (homologyMap (moduleComplexIso f g M hM).hom n) ≫
      (((((Scheme.Modules.pushforward (f ≫ g)).mapHomologicalComplex _).obj
        (injectiveResolution M).cocomplex).sc n).mapHomologyIso (moduleToSheaf B)).inv =
      (forgottenHomologyIso f g M hM n).hom := by
  have h := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor _ (ComplexShape.up ℕ) n).map (moduleComplexIso f g M hM).hom)
    (moduleToSheaf B)
  have hi : ShortComplex.homologyMap
      ((moduleToSheaf B).mapShortComplex.map
        ((shortComplexFunctor _ (ComplexShape.up ℕ) n).map
          (moduleComplexIso f g M hM).hom)) = 𝟙 _ := by
    change homologyMap (((moduleToSheaf B).mapHomologicalComplex _).map
      (moduleComplexIso f g M hM).hom) n = _
    rw [moduleComplexIso_forget]
    exact homologyMap_id _ n
  rw [hi] at h
  dsimp only [forgottenHomologyIso, Iso.symm_hom, homologyMap, homology,
    shortComplexFunctor, shortComplexFunctor', Functor.mapShortComplex,
    Functor.mapHomologicalComplex, sc] at h ⊢
  simpa only [Category.comp_id] using h

set_option maxHeartbeats 800000 in
-- The cancellation compares the module-derived objects with their abelian computations.
/-- Forgetting the module composition gives the square with the abelian comparison. -/
lemma moduleIso_comparison (n : ℕ) :
    (moduleToSheaf B).map (moduleIso f g M hM n).hom ≫
      (comparisonObj (f ≫ g) M n).hom =
    (comparisonObj g ((Scheme.Modules.pushforward f).obj M) n).hom ≫
      (abelianIso f.base g.base (moduleAbelianSheaf M)
        (modulePushforwardAcyclic_abelian f M hM) n).hom := by
  have := isIso_toRightDerived (moduleResolution f M hM) (Scheme.Modules.pushforward g)
    (moduleResolution_acyclic f g M hM) n
  have ht : (moduleToSheaf B).map
      ((moduleResolution f M hM).toRightDerived (Scheme.Modules.pushforward g) n) ≫
      (comparisonObj g ((Scheme.Modules.pushforward f).obj M) n).hom ≫
      (abelianIso f.base g.base (moduleAbelianSheaf M)
        (modulePushforwardAcyclic_abelian f M hM) n).hom =
      (forgottenHomologyIso f g M hM n).hom ≫
        (underlyingResolution M).toRightDerived (abelianPushforward (f ≫ g)) n := by
    rw [← Category.assoc, toRightDerived_forget, Category.assoc, toRightDerived_abelianIso]
  rw [← cancel_epi ((moduleToSheaf B).map
    ((moduleResolution f M hM).toRightDerived (Scheme.Modules.pushforward g) n)), ht]
  simp only [moduleIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  change (moduleToSheaf B).map (isoRightDerivedObj (moduleResolution f M hM)
    (Scheme.Modules.pushforward g) (moduleResolution_acyclic f g M hM) n).inv ≫ _ = _
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [comparisonObj, moduleComputation, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  rw [← (moduleToSheaf B).map_comp_assoc
    ((injectiveResolution M).isoRightDerivedObj (Scheme.Modules.pushforward (f ≫ g)) n).inv
    ((injectiveResolution M).isoRightDerivedObj (Scheme.Modules.pushforward (f ≫ g)) n).hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [homologyFunctor_map]
  rw [← Category.assoc, moduleComplexHomology_forget]
  rfl

/-- The actual module comparison forgets to the sheafified open comparison. -/
lemma moduleIso_hom_forget (n : ℕ) :
    (moduleToSheaf B).map (moduleIso f g M hM n).hom = (forgottenIso f g M hM n).hom := by
  rw [← cancel_mono (comparisonObj (f ≫ g) M n).hom]
  simpa only [forgottenIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using moduleIso_comparison f g M hM n

/-- The inverse comparison is compatible with forgetting as well. -/
lemma moduleIso_inv_forget (n : ℕ) :
    (moduleToSheaf B).map (moduleIso f g M hM n).inv = (forgottenIso f g M hM n).inv := by
  rw [← cancel_mono (forgottenIso f g M hM n).hom, ← moduleIso_hom_forget,
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    moduleIso_hom_forget, Iso.inv_hom_id]

/-- On every base open, the sheafified comparison respects the actual module action. -/
lemma forgottenIso_hom_smul (n : ℕ) (U : B.Opens) (r : Γ(B, U))
    (x : (((Scheme.Modules.pushforward g).rightDerived n).obj
      ((Scheme.Modules.pushforward f).obj M)).val.obj (Opposite.op U)) :
    (forgottenIso f g M hM n).hom.hom.app (Opposite.op U) (r • x) =
      r • (show (((Scheme.Modules.pushforward (f ≫ g)).rightDerived n).obj M).val.obj
        (Opposite.op U) from (forgottenIso f g M hM n).hom.hom.app (Opposite.op U) x) := by
  rw [← moduleIso_hom_forget]
  exact ((moduleIso f g M hM n).hom.val.app (Opposite.op U)).hom.map_smul r x

end FLT.Mazur.RelativeDirectImageForgetting

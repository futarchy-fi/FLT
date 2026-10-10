/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModulePullbackSections
public import FLT.Mazur.ModuleGlobalEvaluationPullback
public import Mathlib.RingTheory.LocalProperties.Projective

/-!
# Finite free trivializations of tilde on principal opens

A basis of a principal localization gives a genuine finite free sheaf
trivialization, on both the localization spectrum and the actual basic open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry PrimeSpectrum
open Scheme.Modules
open scoped TensorProduct
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.TildeFiniteFreeLocalization
universe u
variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (r : R)

/-- Scalar extension to a principal localization is the localized module. -/
def localizationEquiv :
    (ModuleCat.extendScalars (algebraMap R (Localization.Away r))).obj M ≃ₗ[Localization.Away r]
      LocalizedModule.Away r M := by
  let φ := algebraMap R (Localization.Away r)
  let S' := (ModuleCat.restrictScalars φ).obj
    (ModuleCat.of (Localization.Away r) (Localization.Away r))
  let a : S' ≃ₗ[R] Localization.Away r :=
    { AddEquiv.refl _ with
      map_smul' := fun c d ↦ (Algebra.smul_def c (show Localization.Away r from d)).symm }
  let b := TensorProduct.congr a (LinearEquiv.refl R M)
  let c : (ModuleCat.extendScalars φ).obj M ≃ₗ[Localization.Away r]
      Localization.Away r ⊗[R] M :=
    { b.toAddEquiv with
      map_smul' := by
        intro c z
        change b (c • z) = c • b z
        induction z using TensorProduct.inductionOn with
        | tmul s m => rfl
        | add z w hz hw => simpa only [smul_add, map_add] using congrArg₂ (· + ·) hz hw }
  exact c.trans (IsLocalizedModule.isBaseChange (.powers r) (Localization.Away r)
    (LocalizedModule.mkLinearMap (.powers r) M)).equiv

/-- A chosen localized basis trivializes the sheaf over the localization spectrum. -/
def localizationTrivialization {ι : Type u}
    (b : Module.Basis ι (Localization.Away r) (LocalizedModule.Away r M)) :
    (tilde M).restrict (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away r)))) ≅ SheafOfModules.free ι :=
  (restrictFunctorIsoPullback _).app (tilde M) ≪≫
    ((AffineModulePullbackSections.tildePullbackIso _).app M).symm ≪≫
    (tilde.functor _).mapIso ((localizationEquiv M r).trans b.repr).toModuleIso ≪≫
    tildeFinsupp ι

/-- A localized basis also trivializes on the original scheme's basic open. -/
def basicOpenTrivialization {ι : Type u}
    (b : Module.Basis ι (Localization.Away r) (LocalizedModule.Away r M)) :
    (tilde M).restrict (Scheme.Opens.ι (X := Spec R) (basicOpen r)) ≅
      SheafOfModules.free ι := by
  let e := basicOpenIsoSpecAway r
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  exact (restrictFunctorCongr (basicOpenIsoSpecAway_hom_SpecMap r).symm).app (tilde M) ≪≫
    (restrictFunctorComp e.hom f).app (tilde M) ≪≫
    (restrictFunctor e.hom).mapIso (localizationTrivialization M r b) ≪≫
    (restrictFunctorIsoPullback e.hom).app _ ≪≫
    ModuleGlobalEvaluationPullback.freeIso e.hom ι

/-- A finite free principal localization supplies an actual finite free trivialization. -/
theorem exists_basicOpenTrivialization [Module.Finite R M]
    [Module.Free (Localization.Away r) (LocalizedModule.Away r M)] :
    ∃ (ι : Type u), Finite ι ∧ Nonempty
      ((tilde M).restrict (Scheme.Opens.ι (X := Spec R) (basicOpen r)) ≅
        SheafOfModules.free ι) := by
  let ι := Module.Free.ChooseBasisIndex (Localization.Away r) (LocalizedModule.Away r M)
  exact ⟨ι, inferInstance, ⟨basicOpenTrivialization M r (Module.Free.chooseBasis _ _)⟩⟩

end FLT.Mazur.TildeFiniteFreeLocalization

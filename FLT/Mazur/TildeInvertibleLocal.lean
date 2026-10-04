/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleGlobalSections
public import FLT.Mazur.ModuleLineBundlePullback
public import Mathlib.RingTheory.PicardGroup

/-!
# Local triviality of tilde for invertible modules

A finite principal localization cover of an invertible module gives actual
trivializations of its tilde sheaf. No local triviality hypothesis is imposed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry PrimeSpectrum
open Scheme.Modules
open scoped TensorProduct

universe u

namespace FLT.Mazur.SchemePicard

open FCurve AffineModulePullbackSections AffineModuleGlobalSections

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) [Module.Invertible R M]

/-- A free principal localization trivializes the pullback to its spectrum. -/
def tildeLocalizationTrivialization (r : R)
    [Module.Free (Localization.Away r) (LocalizedModule.Away r M)] :
    (tilde M).restrict (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away r)))) ≅
      structureModule (Spec (CommRingCat.of (Localization.Away r))) := by
  let φ := CommRingCat.ofHom (algebraMap R (Localization.Away r))
  let e : (ModuleCat.extendScalars φ.hom).obj M ≃ₗ[Localization.Away r]
      LocalizedModule.Away r M := by
    let S' := (ModuleCat.restrictScalars φ.hom).obj
      (ModuleCat.of (Localization.Away r) (Localization.Away r))
    let a : S' ≃ₗ[R] Localization.Away r :=
      { AddEquiv.refl _ with
        map_smul' := fun c d ↦ (Algebra.smul_def c (show Localization.Away r from d)).symm }
    let b := TensorProduct.congr a (LinearEquiv.refl R M)
    let c : (ModuleCat.extendScalars φ.hom).obj M ≃ₗ[Localization.Away r]
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
  let t := (Module.Invertible.free_iff_linearEquiv.mp
    (inferInstance : Module.Free (Localization.Away r) (LocalizedModule.Away r M))).some
  exact (restrictFunctorIsoPullback (Spec.map φ)).app (tilde M) ≪≫
    ((AffineModulePullbackSections.tildePullbackIso φ).app M).symm ≪≫
    (tilde.functor _).mapIso (e.trans t).toModuleIso ≪≫ tildeSelf

/-- The same trivialization on the actual principal open subscheme. -/
def tildeBasicOpenTrivialization (r : R)
    [Module.Free (Localization.Away r) (LocalizedModule.Away r M)] :
    (tilde M).restrict (Scheme.Opens.ι (X := Spec R) (basicOpen r)) ≅
      structureModule (Scheme.Opens.toScheme (X := Spec R) (basicOpen r)) := by
  let e := basicOpenIsoSpecAway r
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  exact (restrictFunctorCongr (basicOpenIsoSpecAway_hom_SpecMap r).symm).app (tilde M) ≪≫
    (restrictFunctorComp e.hom f).app (tilde M) ≪≫
    (restrictFunctor e.hom).mapIso (tildeLocalizationTrivialization M r) ≪≫
    restrictUnitIso e.hom

/-- Tilde of an invertible ring module is locally free of rank one. -/
theorem tilde_locallyFreeRankOne : LocallyFreeRankOne (tilde M) := by
  obtain ⟨s, hs, hfree⟩ := Module.Invertible.exists_finset_free_localization R M
  have hcov : (⨆ r : s, basicOpen (r : R)) = ⊤ := by
    apply iSup_basicOpen_eq_top_iff.mpr
    convert hs using 2
    ext r
    simp
  intro x
  have hx : x ∈ ⨆ r : s, basicOpen (r : R) := by rw [hcov]; trivial
  obtain ⟨r, hr⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have := hfree r r.property
  exact ⟨basicOpen (r : R), hr, ⟨tildeBasicOpenTrivialization M r⟩⟩

/-- Tilde on any affine scheme carries invertible modules to line bundles. -/
theorem affineTilde_locallyFreeRankOne (X : Scheme.{u}) [IsAffine X]
    (N : ModuleCat Γ(X, ⊤)) [Module.Invertible Γ(X, ⊤) N] :
    LocallyFreeRankOne ((affineTilde X).obj N) :=
  (tilde_locallyFreeRankOne N).pullback X.isoSpec.hom

end FLT.Mazur.SchemePicard

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModulePullbackSections

/-!
# Global-section adjunction on an arbitrary affine scheme

Transport the tilde adjunction through the canonical affine scheme isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineModuleGlobalSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Global sections valued in modules over the actual global-section ring. -/
def sections (X : Scheme.{u}) : X.Modules ⥤ ModuleCat Γ(X, ⊤) :=
  SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op ⊤)

/-- Global sections of pushforward are restriction of scalars. -/
def pushforwardSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pushforward f ⋙ sections Y ≅ sections X ⋙ ModuleCat.restrictScalars f.appTop.hom :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by cat_disch)

/-- The coefficient action on the canonical affine pushforward is the original action. -/
lemma affinePushforward_smul (X : Scheme.{u}) [IsAffine X] (M : X.Modules)
    (r : Γ(X, ⊤)) (m : moduleSpecΓFunctor.obj ((pushforward X.isoSpec.hom).obj M)) :
    r • m = r • (show Γ(M, ⊤) from m) := by
  rw [smul_Spec_def]
  change X.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(X, ⊤)).inv r) • (show Γ(M, ⊤) from m) = _
  change X.toSpecΓ.appTop ((Scheme.ΓSpecIso Γ(X, ⊤)).inv r) • (show Γ(M, ⊤) from m) = _
  rw [Scheme.toSpecΓ_appTop]
  simp

/-- Affine-coordinate global sections identify with the actual sections. -/
def affineSectionsIso (X : Scheme.{u}) [IsAffine X] :
    pushforward X.isoSpec.hom ⋙ moduleSpecΓFunctor ≅ sections X :=
  NatIso.ofComponents (fun M ↦
    (LinearEquiv.ofBijective
      ({ toFun := fun m ↦ m
         map_add' := fun _ _ ↦ rfl
         map_smul' := affinePushforward_smul X M } :
        moduleSpecΓFunctor.obj ((pushforward X.isoSpec.hom).obj M) →ₗ[Γ(X, ⊤)] Γ(M, ⊤))
      Function.bijective_id).toModuleIso) (by cat_disch)

/-- Tilde on the actual affine scheme. -/
def affineTilde (X : Scheme.{u}) [IsAffine X] : ModuleCat Γ(X, ⊤) ⥤ X.Modules :=
  tilde.functor Γ(X, ⊤) ⋙ pullback X.isoSpec.hom

/-- Tilde on an affine scheme is left adjoint to its actual global sections. -/
def affineAdjunction (X : Scheme.{u}) [IsAffine X] : affineTilde X ⊣ sections X :=
  (tilde.adjunction.comp (pullbackPushforwardAdjunction X.isoSpec.hom)).ofNatIsoRight
    (affineSectionsIso X)

/-- Pullback along a scheme isomorphism is an equivalence of module sheaves. -/
def pullbackEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (pullback e.hom) (pullback e.inv)
    ((pullbackComp e.inv e.hom) ≪≫ pullbackCongr e.inv_hom_id ≪≫ pullbackId Y).symm
    ((pullbackComp e.hom e.inv) ≪≫ pullbackCongr e.hom_inv_id ≪≫ pullbackId X)

instance (X : Scheme.{u}) [IsAffine X] : (affineTilde X).Full := by
  have : (pullback X.isoSpec.hom).Full :=
    inferInstanceAs (pullbackEquivalence X.isoSpec).functor.Full
  dsimp [affineTilde]
  infer_instance

instance (X : Scheme.{u}) [IsAffine X] : (affineTilde X).Faithful := by
  have : (pullback X.isoSpec.hom).Faithful :=
    inferInstanceAs (pullbackEquivalence X.isoSpec).functor.Faithful
  dsimp [affineTilde]
  infer_instance

instance (X : Scheme.{u}) [IsAffine X] : IsIso (affineAdjunction X).unit :=
  Adjunction.unit_isIso_of_L_fully_faithful _

/-- Quasi-coherent modules are in the essential image of affine tilde. -/
lemma affineTilde_essImage (X : Scheme.{u}) [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] : (affineTilde X).essImage M := by
  let N := M.restrict X.isoSpec.inv
  refine ⟨moduleSpecΓFunctor.obj N, ⟨?_⟩⟩
  exact (pullback X.isoSpec.hom).mapIso
      (asIso N.fromTildeΓ ≪≫ (restrictFunctorIsoPullback X.isoSpec.inv).app M) ≪≫
    (pullbackComp X.isoSpec.hom X.isoSpec.inv).app M ≪≫
    (pullbackCongr X.isoSpec.hom_inv_id).app M ≪≫ (pullbackId X).app M

/-- The actual global-section reconstruction counit is an isomorphism. -/
instance (X : Scheme.{u}) [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((affineAdjunction X).counit.app M) :=
  (affineAdjunction X).isIso_counit_app_iff_mem_essImage.mpr (affineTilde_essImage X M)

/-- Affine tilde takes modules to quasi-coherent sheaves. -/
instance (X : Scheme.{u}) [IsAffine X] (N : ModuleCat Γ(X, ⊤)) :
    ((affineTilde X).obj N).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback X.isoSpec.hom).app (tilde N)) inferInstance

end FLT.Mazur.AffineModuleGlobalSections

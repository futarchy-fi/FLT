/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineModuleGlobalSections

/-!
# Base change of sections on arbitrary affine schemes

The scalar extension of global sections is canonically the global sections of
the actual sheaf pullback. Both schemes are affine; no flatness assumption is
needed for this local comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped ChangeOfRings
universe u
namespace FLT.Mazur.AffineQuasiCoherentBaseChange
open FLT.Mazur.AffineModuleGlobalSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)

/-- The scalar extension and affine tilde composite has the pullback right adjoint. -/
def scalarTildeAdjunction :
    ModuleCat.extendScalars f.appTop.hom ⋙ affineTilde X ⊣ pushforward f ⋙ sections Y :=
  ((ModuleCat.extendRestrictScalarsAdj f.appTop.hom).comp (affineAdjunction X)).ofNatIsoRight
    (pushforwardSectionsIso f).symm

/-- The natural affine tilde pullback comparison. -/
def tildePullbackIso :
    ModuleCat.extendScalars f.appTop.hom ⋙ affineTilde X ≅ affineTilde Y ⋙ pullback f :=
  (scalarTildeAdjunction f).leftAdjointUniq
    ((affineAdjunction Y).comp (pullbackPushforwardAdjunction f))

/-- Quasi-coherent pullback is reconstructed from the scalar extension of actual sections. -/
def pullbackIso (M : Y.Modules) [M.IsQuasicoherent] :
    (affineTilde X).obj ((ModuleCat.extendScalars f.appTop.hom).obj ((sections Y).obj M)) ≅
      (pullback f).obj M :=
  (tildePullbackIso f).app _ ≪≫
    (pullback f).mapIso (asIso ((affineAdjunction Y).counit.app M))

/-- The affine sheaf base-change isomorphism on actual global-section rings. -/
def sectionsIso (M : Y.Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars f.appTop.hom).obj ((sections Y).obj M) ≅
      (sections X).obj ((pullback f).obj M) :=
  asIso ((affineAdjunction X).unit.app _) ≪≫ (sections X).mapIso (pullbackIso f M)

/-- The tilde pullback comparison respects the adjunction units. -/
lemma tildePullbackIso_unit (N : ModuleCat Γ(Y, ⊤)) (n : N) :
    (sections X).map ((tildePullbackIso f).hom.app N)
      ((affineAdjunction X).unit.app _
        ((ModuleCat.extendRestrictScalarsAdj f.appTop.hom).unit.app N n)) =
    ((pullbackPushforwardAdjunction f).unit.app ((affineTilde Y).obj N)).app ⊤
      ((affineAdjunction Y).unit.app N n) := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app (scalarTildeAdjunction f)
    ((affineAdjunction Y).comp (pullbackPushforwardAdjunction f)) N
  rw [scalarTildeAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv, Adjunction.comp_unit_app] at h
  exact congrArg (fun k ↦ k n) h

/-- The comparison sends a unit tensor to the actual sheaf pullback section. -/
lemma sectionsIso_unit (M : Y.Modules) [M.IsQuasicoherent] (m : Γ(M, ⊤)) :
    (sectionsIso f M).hom
      ((ModuleCat.extendRestrictScalarsAdj f.appTop.hom).unit.app _ m) =
      ((pullbackPushforwardAdjunction f).unit.app M).app ⊤ m := by
  change ((pullback f).map ((affineAdjunction Y).counit.app M)).app ⊤
    ((sections X).map ((tildePullbackIso f).hom.app _)
      ((affineAdjunction X).unit.app _
        ((ModuleCat.extendRestrictScalarsAdj f.appTop.hom).unit.app _ m))) = _
  rw [tildePullbackIso_unit]
  have h := congrArg (fun k ↦ k.app ⊤ ((affineAdjunction Y).unit.app _ m))
    ((pullbackPushforwardAdjunction f).unit.naturality ((affineAdjunction Y).counit.app M))
  change _ = ((pullback f).map ((affineAdjunction Y).counit.app M)).app ⊤ _ at h
  erw [← h]
  have ht := congrArg (fun k ↦ k m) ((affineAdjunction Y).right_triangle_components M)
  exact congrArg (((pullbackPushforwardAdjunction f).unit.app M).app ⊤) ht

/-- The section comparison multiplies each actual pulled-back section by the tensor scalar. -/
lemma sectionsIso_tmul (M : Y.Modules) [M.IsQuasicoherent]
    (s : Γ(X, ⊤)) (m : Γ(M, ⊤)) :
    (sectionsIso f M).hom (s ⊗ₜ[Γ(Y, ⊤),f.appTop.hom] m) =
      s • (show Γ((pullback f).obj M, ⊤) from
        ((pullbackPushforwardAdjunction f).unit.app M).app ⊤ m) := by
  have h := (sectionsIso f M).hom.hom.map_smul s
    (show (ModuleCat.extendScalars f.appTop.hom).obj ((sections Y).obj M) from
      (1 : Γ(X, ⊤)) ⊗ₜ[Γ(Y, ⊤),f.appTop.hom] m)
  have ht : s • ((1 : Γ(X, ⊤)) ⊗ₜ[Γ(Y, ⊤),f.appTop.hom] m :
      (ModuleCat.extendScalars f.appTop.hom).obj ((sections Y).obj M)) =
      s ⊗ₜ[Γ(Y, ⊤),f.appTop.hom] m := by
    exact (ModuleCat.ExtendScalars.smul_tmul f.appTop.hom s 1 m).trans
      (congrArg (fun a : Γ(X, ⊤) ↦ a ⊗ₜ[Γ(Y, ⊤),f.appTop.hom] m) (mul_one s))
  calc
    _ = s • (sectionsIso f M).hom ((1 : Γ(X, ⊤)) ⊗ₜ[Γ(Y, ⊤),f.appTop.hom] m) :=
      (congrArg (sectionsIso f M).hom ht).symm.trans h
    _ = _ := congrArg (fun n : Γ((pullback f).obj M, ⊤) ↦ s • n) (sectionsIso_unit f M m)

/-- Pullback between arbitrary affine schemes preserves quasi-coherence. -/
theorem isQuasicoherent_pullback (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (pullbackIso f M) inferInstance

end FLT.Mazur.AffineQuasiCoherentBaseChange

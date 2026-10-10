/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompactSeparatedPushforward
public import FLT.Mazur.ProperLineFiberVanishing

/-!
# Actual proper direct images as tilde of finite projective sections

The reconstruction is the affine global-section adjunction counit. Positive
acyclicity of the actual residue fibers makes its coefficient module finite
projective, without choosing a very ample presentation of the line family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow AffineModuleGlobalSections

variable {X S : Scheme.{0}} [IsAffine S] (f : X ⟶ S) [IsProper f] (M : X.Modules)

/-- A proper direct image on an affine base is quasi-coherent. -/
theorem properPushforward_isQuasicoherent [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  let _ := QuasiCompact.compactSpace_of_compactSpace f
  let _ : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from f]
    infer_instance⟩
  exact compactSeparatedPushforward_isQuasicoherent M f

/-- Actual direct-image global sections are the original base-linear sections. -/
def properPushforwardSectionsEquiv :
    (sections S).obj ((pushforward f).obj M) ≃ₗ[Γ(S, ⊤)]
      baseSections M f.appTop.hom ⊤ :=
  { AddEquiv.refl _ with
    map_smul' := fun r s ↦ by
      change f.appTop r • (show Γ(M, ⊤) from s) =
        X.presheaf.map (𝟙 _ ) (f.appTop r) • (show Γ(M, ⊤) from s)
      simp only [CategoryTheory.Functor.map_id, CommRingCat.id_apply] }

/-- The reconstruction counit identifies the actual direct image with affine tilde. -/
def properPushforwardTildeIso [M.IsQuasicoherent] :
    (affineTilde S).obj (ModuleCat.of Γ(S, ⊤) (baseSections M f.appTop.hom ⊤)) ≅
      (pushforward f).obj M := by
  let _ := properPushforward_isQuasicoherent f M
  exact (affineTilde S).mapIso (properPushforwardSectionsEquiv f M).symm.toModuleIso ≪≫
    asIso ((affineAdjunction S).counit.app ((pushforward f).obj M))

variable [IsNoetherianRing Γ(S, ⊤)] [Flat f] (L : X.Modules)
  (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

include hL in
omit [Flat f] in
/-- The coefficient module of the actual direct image is finite. -/
theorem properPushforwardSections_finite :
    Module.Finite Γ(S, ⊤) ((sections S).obj ((pushforward f).obj L)) := by
  let _ := hL.isFinitePresentation
  let _ := proper_sections_finite f L
  exact Module.Finite.equiv (properPushforwardSectionsEquiv f L).symm

include hL hV in
/-- Residue-fiber vanishing makes the actual direct-image module projective. -/
theorem properPushforwardSections_projective :
    Module.Projective Γ(S, ⊤) ((sections S).obj ((pushforward f).obj L)) := by
  let _ := projective_sections_of_residue_fibers f L hL hV
  exact Module.Projective.of_equiv (properPushforwardSectionsEquiv f L).symm

/-- The reconstructed proper line direct image, with its original section module. -/
def properLinePushforwardTildeIso :
    (affineTilde S).obj (ModuleCat.of Γ(S, ⊤) (baseSections L f.appTop.hom ⊤)) ≅
      (pushforward f).obj L := by
  let _ := hL.isFinitePresentation
  exact properPushforwardTildeIso f L

end FLT.Mazur.LineSectionBaseChange

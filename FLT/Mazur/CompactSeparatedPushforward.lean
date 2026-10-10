/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionBaseLocalization
public import FLT.Mazur.AffineModuleGlobalSections

/-!
# Quasi-coherent direct images from compact separated schemes

Localization of actual sections identifies the direct image over a spectrum
with the tilde of its global sections. Transport gives the same result over
an arbitrary affine base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open Chow
variable {X : Scheme} {R : CommRingCat} (f : X ⟶ Spec R) (M : X.Modules)

/-- Direct-image sections carry exactly the structural action of the base ring. -/
def pushforwardBaseSectionsEquiv (U : (Spec R).Opens) :
    Γ((pushforward f).obj M, U) ≃ₗ[R] baseSections M (affineBaseScalars f) (f ⁻¹ᵁ U) where
  toFun s := s
  invFun s := s
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r s := by
    change f.app U ((Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv r)) •
      (show Γ(M, f ⁻¹ᵁ U) from s) = _
    have h := congr($(f.naturality U.leTop.op) ((Scheme.ΓSpecIso R).inv r))
    exact congrArg (fun a ↦ a • (show Γ(M, f ⁻¹ᵁ U) from s)) h

/-- Localization of sections makes the actual direct image localizing. -/
theorem compactSeparatedPushforward_isLocalizing [M.IsQuasicoherent]
    [CompactSpace X] [X.IsSeparated] :
    IsLocalizing (modulesSpecToSheaf.obj ((pushforward f).obj M)) := by
  intro r
  let e := pushforwardBaseSectionsEquiv f M ⊤
  let e' := pushforwardBaseSectionsEquiv f M (PrimeSpectrum.basicOpen r)
  have h := sectionBaseRestriction_isLocalized f M r
  have h' := IsLocalizedModule.of_linearEquiv (.powers r)
    (baseRestriction M (affineBaseScalars f) (show f ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ ⊤
      from le_top)) e'.symm
  have h'' := (IsLocalizedModule.comp_iff_of_bijective_right (.powers r)
    e.toLinearMap e.bijective).mpr h'
  exact h''

/-- Quasi-coherence of the actual direct image over a spectrum. -/
theorem compactSeparatedPushforwardSpec_isQuasicoherent [M.IsQuasicoherent]
    [CompactSpace X] [X.IsSeparated] : ((pushforward f).obj M).IsQuasicoherent :=
  (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr
    ((isIso_fromTildeΓ_iff_isLocalizing _).mpr
      (compactSeparatedPushforward_isLocalizing f M))

/-- Quasi-coherence of the actual direct image over any affine base. -/
theorem compactSeparatedPushforward_isQuasicoherent {S : Scheme} [IsAffine S]
    (g : X ⟶ S) [M.IsQuasicoherent] [CompactSpace X] [X.IsSeparated] :
    ((pushforward g).obj M).IsQuasicoherent := by
  let N := (pushforward (g ≫ S.isoSpec.hom)).obj M
  let _ : N.IsQuasicoherent := compactSeparatedPushforwardSpec_isQuasicoherent _ M
  let e : (pushforward S.isoSpec.inv).obj N ≅ (pushforward g).obj M :=
    (pushforwardComp (g ≫ S.isoSpec.hom) S.isoSpec.inv).app M ≪≫
      (pushforwardCongr (by simp)).app M
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso e
    (quasicoherent_pushforwardIso S.isoSpec.symm N)

end FLT.Mazur.FCurve

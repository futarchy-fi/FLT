/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafTensorAffine
public import FLT.Mazur.AffinePushforwardQuasicoherent

/-!
# Principal localization of affine-piece sections in arbitrary universes

The original restrictions on any affine source open are localization over
an affine base. The scalar ring and schemes may live in any common universe.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace FLT.Mazur.AffinePieceSectionLocalization

section Scalars
variable {Y : Scheme.{u}} {R : Type u} [CommRing R]
variable (M : Y.Modules) (ρ : R →+* Γ(Y, ⊤))

/-- Sections on an open with scalars induced by a fixed base-ring map. -/
abbrev baseSections (W : Y.Opens) : ModuleCat R :=
  (ModuleCat.restrictScalars ((Y.presheaf.map W.leTop.op).hom.comp ρ)).obj (M.val.obj (op W))

/-- Actual restriction of sections is linear for the fixed base-ring action. -/
def baseRestriction {W T : Y.Opens} (h : W ≤ T) :
    baseSections M ρ T →ₗ[R] baseSections M ρ W where
  toFun := M.presheaf.map (homOfLE h).op
  map_add' := map_add _
  map_smul' r s := by
    change M.presheaf.map (homOfLE h).op ((Y.presheaf.map T.leTop.op) (ρ r) • s) =
      (Y.presheaf.map W.leTop.op) (ρ r) • M.presheaf.map (homOfLE h).op s
    rw [M.map_smul]
    congr 1
    exact congr($((Y.presheaf.map_comp T.leTop.op (homOfLE h).op).symm) (ρ r))

end Scalars

variable {Y : Scheme.{u}} {R : CommRingCat.{u}} (M : Y.Modules) (a : Y ⟶ Spec R)

/-- The scalar map induced by a morphism to an affine scheme. -/
def affineBaseScalars : R →+* Γ(Y, ⊤) :=
  ((Scheme.ΓSpecIso R).inv ≫ a.appTop).hom

/-- The image of the inverse-image open inside a piece is its intersection. -/
lemma affinePiece_image (W : Y.Opens) (U : (Spec R).Opens) :
    W.ι ''ᵁ ((W.ι ≫ a) ⁻¹ᵁ U) = W ⊓ a ⁻¹ᵁ U := by
  simp [Scheme.Hom.image_preimage_eq_opensRange_inf]

/-- Additive coordinates of sections on an affine piece. -/
def affinePieceSectionsAddIso (W : Y.Opens) (U : (Spec R).Opens) :
    Γ((pushforward (W.ι ≫ a)).obj (M.restrict W.ι), U) ≅
      Γ(M, W ⊓ a ⁻¹ᵁ U) :=
  M.restrictAppIso W.ι _ ≪≫
    M.presheaf.mapIso (eqToIso (affinePiece_image a W U).symm).op

/-- Piece coordinates retain the actual structural action of the base ring. -/
lemma affinePieceSectionsAddIso_smul (W : Y.Opens) (U : (Spec R).Opens)
    (r : R) (s : Γ((pushforward (W.ι ≫ a)).obj (M.restrict W.ι), U)) :
    (affinePieceSectionsAddIso M a W U).hom (r • s) =
      ((Y.presheaf.map (W ⊓ a ⁻¹ᵁ U).leTop.op).hom (affineBaseScalars a r)) •
        (affinePieceSectionsAddIso M a W U).hom s := by
  change M.presheaf.map _ ((W.ι.appIso _).inv
    ((W.ι ≫ a).app U ((Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv r))) •
      (show Γ(M, W.ι ''ᵁ ((W.ι ≫ a) ⁻¹ᵁ U)) from s)) = _
  rw [Scheme.Opens.ι_appIso]
  erw [M.map_smul]
  congr 1
  simp only [Scheme.Hom.comp_app, CommRingCat.comp_apply, Scheme.Opens.ι_app,
    Iso.refl_inv]
  change Y.presheaf.map _ (Y.presheaf.map _
    (a.app U ((Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv r)))) = _
  have hn := congr($(a.naturality U.leTop.op) ((Scheme.ΓSpecIso R).inv r))
  change a.app U ((Spec R).presheaf.map U.leTop.op ((Scheme.ΓSpecIso R).inv r)) = _ at hn
  rw [hn]
  simp only [affineBaseScalars, CommRingCat.hom_comp, RingHom.comp_apply,
    ← Functor.map_comp_apply, ← op_comp]
  rfl

/-- Linear coordinates of the direct-image sections on every base open. -/
def affinePieceSectionsEquiv (W : Y.Opens) (U : (Spec R).Opens) :
    Γ((pushforward (W.ι ≫ a)).obj (M.restrict W.ι), U) ≃ₗ[R]
      baseSections M (affineBaseScalars a) (W ⊓ a ⁻¹ᵁ U) :=
  { (affinePieceSectionsAddIso M a W U).addCommGroupIsoToAddEquiv with
    map_smul' := affinePieceSectionsAddIso_smul M a W U }

/-- The piece coordinates intertwine restriction on any pair of base opens. -/
lemma affinePieceSectionsEquiv_restriction (W : Y.Opens)
    {U T : (Spec R).Opens} (h : U ≤ T)
    (s : Γ((pushforward (W.ι ≫ a)).obj (M.restrict W.ι), T)) :
    affinePieceSectionsEquiv M a W U
      (((pushforward (W.ι ≫ a)).obj (M.restrict W.ι)).presheaf.map (homOfLE h).op s) =
    baseRestriction M (affineBaseScalars a)
      (inf_le_inf_left W ((Opens.map a.base).map (homOfLE h)).le)
      (affinePieceSectionsEquiv M a W T s) := by
  change M.presheaf.map (eqToHom (affinePiece_image a W U).symm).op
    ((M.restrict W.ι).presheaf.map
      ((Opens.map (W.ι ≫ a).base).map (homOfLE h)).op s) =
    M.presheaf.map (homOfLE _).op
      (M.presheaf.map (eqToHom (affinePiece_image a W T).symm).op s)
  rw [Scheme.Modules.restrict_map]
  erw [← Functor.map_comp_apply]
  simp only [← Functor.map_comp_apply, ← op_comp]
  rfl

/-- Equality of opens transports localization with all scalar instances intact. -/
lemma baseRestriction_isLocalized_congr {Z : Scheme.{u}} {S : Type u} [CommRing S]
    (N : Z.Modules) (ρ : S →+* Γ(Z, ⊤)) (r : S)
    {W T W' T' : Z.Opens} (h : W ≤ T) (h' : W' ≤ T')
    (hW : W = W') (hT : T = T') :
    IsLocalizedModule (.powers r) (baseRestriction N ρ h) ↔
      IsLocalizedModule (.powers r) (baseRestriction N ρ h') := by
  subst W'; subst T'; rfl

/-- Localization in affine-piece coordinates is the actual base restriction. -/
theorem affinePiece_baseRestriction_isLocalized (W : Y.Opens) (r : R)
    [IsLocalizedModule (.powers r) (ModuleSheafTensor.affineRestriction
      ((pushforward (W.ι ≫ a)).obj (M.restrict W.ι)) r)] :
    IsLocalizedModule (.powers r) (baseRestriction M (affineBaseScalars a)
      (show W ⊓ a ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ W from inf_le_left)) := by
  let e := affinePieceSectionsEquiv M a W ⊤
  let e' := affinePieceSectionsEquiv M a W (PrimeSpectrum.basicOpen r)
  have h := IsLocalizedModule.of_linearEquiv (.powers r)
    (ModuleSheafTensor.affineRestriction ((pushforward (W.ι ≫ a)).obj (M.restrict W.ι)) r) e'
  have h' : IsLocalizedModule (.powers r)
      ((baseRestriction M (affineBaseScalars a)
        (inf_le_inf_left W ((Opens.map a.base).map
          (homOfLE (show PrimeSpectrum.basicOpen r ≤ ⊤ from le_top))).le)).comp
        e.toLinearMap) := by
    convert h using 1
    ext s
    exact (affinePieceSectionsEquiv_restriction M a W le_top s).symm
  have h'' := (IsLocalizedModule.comp_iff_of_bijective_right (.powers r)
    e.toLinearMap e.bijective).mp h'
  exact (baseRestriction_isLocalized_congr M (affineBaseScalars a) r _ _ rfl
    (by change W ⊓ (⊤ : Y.Opens) = W; exact inf_top_eq W)).mp h''

/-- Quasi-coherent sections localize on each actual affine source piece. -/
theorem affinePiece_sectionRestriction_isLocalized [M.IsQuasicoherent]
    (W : Y.Opens) (hW : IsAffineOpen W) (r : R) :
    IsLocalizedModule (.powers r) (baseRestriction M (affineBaseScalars a)
      (show W ⊓ a ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ W from inf_le_left)) := by
  let _ : IsAffine W.toScheme := hW
  let _ : ((pushforward (W.ι ≫ a)).obj (M.restrict W.ι)).IsQuasicoherent :=
    affineSchemePushforward_isQuasicoherent _ _
  exact affinePiece_baseRestriction_isLocalized M a W r

end FLT.Mazur.AffinePieceSectionLocalization

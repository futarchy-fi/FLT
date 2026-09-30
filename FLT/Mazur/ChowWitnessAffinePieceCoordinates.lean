/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowWitnessSectionsLocalization

/-!
# Affine-piece coordinates for Chow witness sections

Sections of an affine-piece direct image identify with the base-linear sections
on that piece. These identifications commute with restriction to principal opens.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules FLT.Mazur.FCurve

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.Chow

section Coordinates

variable {Y : Scheme} {R : CommRingCat} (M : Y.Modules) (a : Y ⟶ Spec R)

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
lemma baseRestriction_isLocalized_congr {Z : Scheme} {S : Type} [CommRing S]
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

end Coordinates

/-- A coefficient isomorphism preserves the fixed base-ring action on every open. -/
def baseSectionsIsoEquiv {Y : Scheme} {R : Type} [CommRing R] {M N : Y.Modules} (e : M ≅ N)
    (ρ : R →+* Γ(Y, ⊤)) (U : Y.Opens) :
    baseSections M ρ U ≃ₗ[R] baseSections N ρ U where
  toFun := (e.hom.app U)
  invFun := (e.inv.app U)
  left_inv s := by
    change ((e.hom ≫ e.inv).app U) s = s
    simp
  right_inv s := by
    change ((e.inv ≫ e.hom).app U) s = s
    simp
  map_add' := map_add _
  map_smul' r s := Hom.app_smul e.hom _ _


variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The base restriction on any affine Chow piece is localization. -/
theorem graphAffinePiece_baseRestriction_isLocalized (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) (W : (graphClosureπ f ⁻¹ᵁ V).toScheme.Opens)
    (hW : IsAffineOpen W) (r : Γ(X, V)) :
    IsLocalizedModule (.powers r) (baseRestriction (graphPowerOver f n V)
      (graphPowerBaseScalars f V hV)
      (show W ⊓ ((graphClosureπ f ∣_ V) ≫ hV.isoSpec.hom) ⁻¹ᵁ
        PrimeSpectrum.basicOpen r ≤ W from inf_le_left)) := by
  have : IsLocalizedModule (.powers r) (ModuleSheafTensor.affineRestriction
      ((pushforward (W.ι ≫ ((graphClosureπ f ∣_ V) ≫ hV.isoSpec.hom))).obj
        ((graphPowerOver f n V).restrict W.ι)) r) := by
    simpa only [graphAffinePiecePushforward, Category.assoc] using
      graphAffinePieceRestriction_isLocalized f n V hV W hW r
  exact affinePiece_baseRestriction_isLocalized _ _ W r

/-- The finite product of chart restrictions localizes in equalizer coordinates. -/
theorem graphBaseProductRestriction_isLocalized (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) (r : Γ(X, V)) :
    IsLocalizedModule (.powers r) (baseProductRestriction (graphPowerOver f n V)
      (graphPowerBaseScalars f V hV) (graphAffineChart f V hV)
      (((graphClosureπ f ∣_ V) ≫ hV.isoSpec.hom) ⁻¹ᵁ PrimeSpectrum.basicOpen r)) := by
  have (i : Fin (graphProjectiveDimension f + 1)) :=
    graphAffinePiece_baseRestriction_isLocalized f n V hV _
      (graphAffineChart_isAffine f V hV i) r
  exact IsLocalizedModule.pi _ _

/-- The finite overlap product localizes with the same scalar action. -/
theorem graphBaseOverlapRestriction_isLocalized (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) (r : Γ(X, V)) :
    IsLocalizedModule (.powers r) (baseOverlapRestriction (graphPowerOver f n V)
      (graphPowerBaseScalars f V hV) (graphAffineChart f V hV)
      (((graphClosureπ f ∣_ V) ≫ hV.isoSpec.hom) ⁻¹ᵁ PrimeSpectrum.basicOpen r)) := by
  let B := ((graphClosureπ f ∣_ V) ≫ hV.isoSpec.hom) ⁻¹ᵁ PrimeSpectrum.basicOpen r
  have (ij : Fin (graphProjectiveDimension f + 1) × Fin (graphProjectiveDimension f + 1)) :
      IsLocalizedModule (.powers r) (baseRestriction (graphPowerOver f n V)
        (graphPowerBaseScalars f V hV) (show
          (graphAffineChart f V hV ij.1 ⊓ B) ⊓ (graphAffineChart f V hV ij.2 ⊓ B) ≤
          graphAffineChart f V hV ij.1 ⊓ graphAffineChart f V hV ij.2 from
            inf_le_inf inf_le_left inf_le_left)) := by
    have h := graphAffinePiece_baseRestriction_isLocalized f n V hV _
      (graphAffineChart_inf_isAffine f V hV ij.1 ij.2) r
    exact (baseRestriction_isLocalized_congr _ _ r _ _
      (by dsimp [B]; simp only [inf_inf_inf_comm, inf_idem]) rfl).mp h
  exact IsLocalizedModule.pi _ _

/-- Localization of actual sections follows from the two finite product calculations. -/
theorem graphPowerOver_baseRestriction_isLocalized (n : ℕ) (V : X.Opens)
    (hV : IsAffineOpen V) (r : Γ(X, V)) :
    IsLocalizedModule (.powers r) (baseRestriction (graphPowerOver f n V)
      (graphPowerBaseScalars f V hV) (show
        ((graphClosureπ f ∣_ V) ≫ hV.isoSpec.hom) ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ ⊤
          from le_top)) := by
  have := graphBaseProductRestriction_isLocalized f n V hV r
  have := graphBaseOverlapRestriction_isLocalized f n V hV r
  exact baseRestriction_isLocalized_of_products _ _ _ (iSup_graphAffineChart f V hV) _ r

end FLT.Mazur.Chow

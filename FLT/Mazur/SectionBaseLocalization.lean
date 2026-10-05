/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowWitnessAffinePieceCoordinates

/-!
# Localization of sections on a quasi-compact separated scheme

A finite affine cover and its affine pairwise intersections compute sections
as an equalizer. Localization is exact and commutes with these finite products,
so sections localize over every principal open of an arbitrary affine base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace FLT.Mazur.FCurve
open Chow
variable {X : Scheme} {R : CommRingCat} (f : X ⟶ Spec R) (M : X.Modules)

/-- A quasi-coherent sheaf is localizing on an affine source piece. -/
theorem affinePiece_sectionRestriction_isLocalized [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (r : R) :
    IsLocalizedModule (.powers r) (baseRestriction M (affineBaseScalars f)
      (show U ⊓ f ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ U from inf_le_left)) := by
  let : IsAffine U.toScheme := hU
  let : ((pushforward (U.ι ≫ f)).obj (M.restrict U.ι)).IsQuasicoherent :=
    affineSchemePushforward_isQuasicoherent _ _
  exact affinePiece_baseRestriction_isLocalized M f U r

/-- The actual global section restriction localizes on every principal base open. -/
theorem sectionBaseRestriction_isLocalized [M.IsQuasicoherent]
    [CompactSpace X] [X.IsSeparated] (r : R) :
    IsLocalizedModule (.powers r) (baseRestriction M (affineBaseScalars f)
      (show f ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ ⊤ from le_top)) := by
  let C := X.affineCover.finiteSubcover
  let U := fun i : C.I₀ ↦ (C.f i).opensRange
  have hU (i) : IsAffineOpen (U i) := isAffineOpen_opensRange (C.f i)
  let B := f ⁻¹ᵁ PrimeSpectrum.basicOpen r
  have (i : C.I₀) := affinePiece_sectionRestriction_isLocalized f M (U i) (hU i) r
  have : IsLocalizedModule (.powers r)
      (baseProductRestriction M (affineBaseScalars f) U B) := IsLocalizedModule.pi _ _
  have (ij : C.I₀ × C.I₀) : IsLocalizedModule (.powers r)
      (baseRestriction M (affineBaseScalars f)
        (show (U ij.1 ⊓ B) ⊓ (U ij.2 ⊓ B) ≤ U ij.1 ⊓ U ij.2 from
          inf_le_inf inf_le_left inf_le_left)) := by
    have h := affinePiece_sectionRestriction_isLocalized f M _ ((hU ij.1).inf (hU ij.2)) r
    exact (baseRestriction_isLocalized_congr _ _ r _ _
      (by
        change (U ij.1 ⊓ U ij.2) ⊓ B = (U ij.1 ⊓ B) ⊓ (U ij.2 ⊓ B)
        exact ((inf_inf_inf_comm _ _ _ _).trans
          (congrArg ((U ij.1 ⊓ U ij.2) ⊓ ·) (inf_idem B))).symm) rfl).mp h
  have : IsLocalizedModule (.powers r)
      (baseOverlapRestriction M (affineBaseScalars f) U B) := IsLocalizedModule.pi _ _
  exact baseRestriction_isLocalized_of_products _ _ _ C.iSup_opensRange B r

/-- Every principal-base section has a global numerator after multiplying by a power. -/
theorem exists_sectionBase_numerator [M.IsQuasicoherent]
    [CompactSpace X] [X.IsSeparated] (r : R)
    (s : baseSections M (affineBaseScalars f) (f ⁻¹ᵁ PrimeSpectrum.basicOpen r)) :
    ∃ (n : ℕ) (t : baseSections M (affineBaseScalars f) ⊤),
      baseRestriction M (affineBaseScalars f) (show f ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ ⊤
        from le_top) t = r ^ n • s := by
  let := sectionBaseRestriction_isLocalized f M r
  obtain ⟨n, t, ht⟩ := IsLocalizedModule.Away.surj
    (baseRestriction M (affineBaseScalars f) (show f ⁻¹ᵁ PrimeSpectrum.basicOpen r ≤ ⊤
      from le_top)) r s
  exact ⟨n, t, ht.symm⟩

end FLT.Mazur.FCurve

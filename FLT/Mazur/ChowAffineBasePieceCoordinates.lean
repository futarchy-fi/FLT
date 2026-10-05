/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowWitnessAffinePieceCoordinates
public import FLT.Mazur.ChowAffineBaseSectionsLocalization

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

namespace FLT.Mazur.Chow.AffineBase

variable {R : CommRingCat} [IsNoetherianRing R] {X : Scheme} (f : X ⟶ Spec R)
  [IsProper f]

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

end FLT.Mazur.Chow.AffineBase

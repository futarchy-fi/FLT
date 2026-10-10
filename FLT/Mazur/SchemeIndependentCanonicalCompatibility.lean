/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfCanonicalPairRecovery
public import FLT.Mazur.SchemeIndependentCanonicalCoordinate
public import FLT.Mazur.SchemeOverlapNormalizationDetection

/-!
# Canonical independent assembly recovers canonical geometric descent

The source comparison respects every original pair. The original pair
cover detects its global compatibility with the constructed overlap.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily.IndependentLineData
open SchemePicard SchemeGeometricDescent SheafPullbackCoordinateRecovery
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] SchemeCoproductModuleGluing.assembled
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
variable (L : LineBundleCat X)

/-- The source comparison intertwines the normalized overlaps on every original pair. -/
lemma canonicalSourceIso_normalized (ij : 𝒰.I₀ × 𝒰.I₀) :
    (canonicalNormalizedPair 𝒰 L.val ij).hom ≫
      (pullback (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2) ≫
        Limits.Sigma.ι 𝒰.X ij.2)).map (canonicalSourceIso 𝒰 L).hom =
    (pullback (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2) ≫
      Limits.Sigma.ι 𝒰.X ij.1)).map (canonicalSourceIso 𝒰 L).hom ≫
        (normalizedPair 𝒰 (fun i ↦ ((canonicalObj 𝒰 L).obj i).val)
          (canonicalObj 𝒰 L).overlap ij).hom := by
  apply (cancel_mono (recovery (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2))
    (Limits.Sigma.ι 𝒰.X ij.2) _ rfl (canonicalObj 𝒰 L).toFamily.obj
    ((canonicalObj 𝒰 L).memberRecovery ij.2)).hom).mp
  rw [Category.assoc, canonicalSourceIso_coordinate]
  change (canonicalNormalizedPair 𝒰 L.val ij).hom ≫
    (canonicalRightRecovery 𝒰 L.val ij).hom = _
  rw [canonicalNormalizedPair_recovery]
  have hr : (normalizedPair 𝒰 (fun i ↦ ((canonicalObj 𝒰 L).obj i).val)
      (canonicalObj 𝒰 L).overlap ij).hom ≫
      (recovery (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2))
        (Limits.Sigma.ι 𝒰.X ij.2) _ rfl (canonicalObj 𝒰 L).toFamily.obj
        ((canonicalObj 𝒰 L).memberRecovery ij.2)).hom =
      (recovery (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2))
        (Limits.Sigma.ι 𝒰.X ij.1) _ rfl (canonicalObj 𝒰 L).toFamily.obj
        ((canonicalObj 𝒰 L).memberRecovery ij.1)).hom ≫
        ((canonicalObj 𝒰 L).overlap ij).hom :=
    normalizedPair_recovery 𝒰 (fun i ↦ ((canonicalObj 𝒰 L).obj i).val)
      (canonicalObj 𝒰 L).overlap ij
  rw [Category.assoc, hr, ← Category.assoc, canonicalSourceIso_coordinate 𝒰 L ij.1]
  rfl

/-- The original pair cover detects compatibility of the canonical source comparison. -/
lemma canonicalSourceIso_compatible :
    (SchemeGeometricDescent.canonical (projection 𝒰) L.val).MapCompatible (projection 𝒰)
      (canonicalObj 𝒰 L).toFamily.datum (canonicalSourceIso 𝒰 L).hom :=
  SchemeOverlapDiagonalChart.compatible_of_normalized_cover
    (Limits.pullback.fst (projection 𝒰) (projection 𝒰))
    (Limits.pullback.snd (projection 𝒰) (projection 𝒰)) (pair 𝒰) (pairMap 𝒰)
    (pair_jointly_covers 𝒰)
    (fun ij ↦ Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2) ≫ Limits.Sigma.ι 𝒰.X ij.1)
    (fun ij ↦ Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2) ≫ Limits.Sigma.ι 𝒰.X ij.2)
    (pairMap_fst 𝒰) (pairMap_snd 𝒰) _ _ (canonicalSourceIso 𝒰 L).hom
    (canonicalSourceIso_normalized 𝒰 L)

/-- Canonical independent assembly is the actual canonical family datum of the base line. -/
def canonicalAssemblyIso :
    (familyLineEquivalence 𝒰).functor.obj L ≅ assemble.obj (canonicalObj 𝒰 L) :=
  LineData.isoMk (projection 𝒰) (canonicalSourceIso 𝒰 L) (canonicalSourceIso_compatible 𝒰 L)

end FLT.Mazur.SchemeFppfFamily.IndependentLineData

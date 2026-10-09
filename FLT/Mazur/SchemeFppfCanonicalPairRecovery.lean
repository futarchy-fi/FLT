/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackCanonicalRecovery
public import FLT.Mazur.SchemeIndependentCanonicalFamily

/-!
# Canonical total overlaps recover the original unequal pairs

The canonical overlap on the coproduct, normalized to an original pair,
intertwines its canonical pair through the actual member comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeFppfFamily
open SheafPullbackPathComparison SheafPullbackCoordinateRecovery
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] projection pairMap
variable {X : Scheme.{u}} (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage X)
variable (A : X.Modules) (ij : 𝒰.I₀ × 𝒰.I₀)

/-- The canonical overlap normalized to the two coordinates of an original pair. -/
def canonicalNormalizedPair :=
  SchemeOverlapDiagonalChart.normalize
    (Limits.pullback.fst (projection 𝒰) (projection 𝒰))
    (Limits.pullback.snd (projection 𝒰) (projection 𝒰)) (pairMap 𝒰 ij)
    (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2) ≫ Limits.Sigma.ι 𝒰.X ij.1)
    (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2) ≫ Limits.Sigma.ι 𝒰.X ij.2)
    (pairMap_fst 𝒰 ij) (pairMap_snd 𝒰 ij) ((pullback (projection 𝒰)).obj A)
    (SchemeGeometricDescent.canonical (projection 𝒰) A).overlap

/-- Recover the first member after normalizing the canonical total overlap. -/
def canonicalLeftRecovery :=
  recovery (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2))
    (Limits.Sigma.ι 𝒰.X ij.1) _ rfl ((pullback (projection 𝒰)).obj A)
    ((comparison (Limits.Sigma.ι 𝒰.X ij.1) (projection 𝒰) (𝒰.f ij.1)
      (inclusion_projection 𝒰 ij.1)).app A)

/-- Recover the second member using its canonical base comparison. -/
def canonicalRightRecovery :=
  recovery (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2))
    (Limits.Sigma.ι 𝒰.X ij.2) _ rfl ((pullback (projection 𝒰)).obj A)
    ((comparison (Limits.Sigma.ι 𝒰.X ij.2) (projection 𝒰) (𝒰.f ij.2)
      (inclusion_projection 𝒰 ij.2)).app A)

/-- The normalized canonical total overlap gives precisely the original canonical pair. -/
lemma canonicalNormalizedPair_recovery :
    (canonicalNormalizedPair 𝒰 A ij).hom ≫ (canonicalRightRecovery 𝒰 A ij).hom =
      (canonicalLeftRecovery 𝒰 A ij).hom ≫
        (SchemeIndependentCanonicalOverlap.pair (𝒰.f ij.1) (𝒰.f ij.2) A).hom := by
  have hl : (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2) ≫
      Limits.Sigma.ι 𝒰.X ij.1) ≫ projection 𝒰 =
        Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2) ≫ 𝒰.f ij.1 := by
    rw [Category.assoc, inclusion_projection]
  have hr : (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2) ≫
      Limits.Sigma.ι 𝒰.X ij.2) ≫ projection 𝒰 =
        Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2) ≫ 𝒰.f ij.1 := by
    rw [Category.assoc, inclusion_projection, Limits.pullback.condition]
  have hn := SchemePullbackOverlap.normalize_overlap_base (projection 𝒰)
    (Limits.pullback.fst (projection 𝒰) (projection 𝒰))
    (Limits.pullback.snd (projection 𝒰) (projection 𝒰))
    (Limits.pullback.fst (projection 𝒰) (projection 𝒰) ≫ projection 𝒰)
    rfl Limits.pullback.condition.symm (pairMap 𝒰 ij) _ _
    (pairMap_fst 𝒰 ij) (pairMap_snd 𝒰 ij)
    (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2) ≫ 𝒰.f ij.1) hl hr A
  change canonicalNormalizedPair 𝒰 A ij = _ at hn
  rw [hn]
  exact overlap_recovery (projection 𝒰) (Limits.Sigma.ι 𝒰.X ij.1)
    (Limits.Sigma.ι 𝒰.X ij.2) (𝒰.f ij.1) (𝒰.f ij.2)
    (inclusion_projection 𝒰 ij.1) (inclusion_projection 𝒰 ij.2)
    (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2))
    (Limits.pullback.snd (𝒰.f ij.1) (𝒰.f ij.2)) _ _ rfl rfl
    (Limits.pullback.fst (𝒰.f ij.1) (𝒰.f ij.2) ≫ 𝒰.f ij.1)
    rfl Limits.pullback.condition.symm hl hr A

end FLT.Mazur.SchemeFppfFamily

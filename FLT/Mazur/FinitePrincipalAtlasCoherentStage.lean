/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasCoverStage
public import FLT.Mazur.PrincipalOccurrenceCoherentRefinement
public import FLT.Mazur.FinitePrincipalAtlasImageStage
public import FLT.Mazur.FinitePrincipalAtlasComparisonStage

/-!
# Simultaneously coherent stages of actual finite affine atlases

The original scheme constructs the target-compatible patch covers and every
outer-image inclusion. These descend together with all actual cross-chart
comparison equations to one bijective stage above prescribed relation bounds.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv principalOccurrenceLocalComparisonLeft
  principalOccurrenceLocalComparisonRight principalOccurrenceCrossEquationTransport
  principalOccurrencePatchOpen principalOccurrenceCrossOuterLeft principalOccurrenceCrossOuterRight
  principalOccurrenceOpenAt relationIdeal chartAlgebra principalRepresentative
  principalOccurrenceStagePreorder finitePrincipalAtlasRoutes

universe u v

variable {R : CommRingCat.{u}} {X : Scheme.{u}} [QuasiSeparatedSpace X]
  {ι : Type v} [Finite ι] (U : ι → X.affineOpens) (f : X ⟶ Spec R) [LocallyOfFiniteType f]

local notation "D" => atlasPrincipalDestination U
local notation "AA" => atlasPrincipalSection U
set_option quotPrecheck false in
local notation "BB" => fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1))
local notation "E" => atlasPrincipalEquiv U f
local notation "OccurrenceStage" =>
  PrincipalOccurrenceStage D AA BB (fun i k ↦ AlgEquiv.toAlgHom (E i k))

/-- The actual finite patch covers, atlas image inclusions and all route equations. -/
def finitePrincipalAtlasStageCoherent :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    (y : OccurrenceStage) → (∀ i k, Function.Bijective (y.hom i k)) →
      (AtlasPrincipalOverlap U → ι) → Prop := by
  intro _ _ _ _ y hy t
  exact
    (∀ j, (⨆ p : PrincipalOccurrencePatchTo (dst := D) j (t j),
      (principalOccurrencePatchOpen y hy p.1).opensRange) = ⊤) ∧
    (∀ j (p q : PrincipalOccurrencePatch (dst := D) j),
      (atlasPrincipalOpen U (D p.1.val.1 p.2)).1 ≤
        (atlasPrincipalOpen U (D q.1.val.1 q.2)).1 →
      (principalOccurrencePatchOpen y hy p).opensRange ≤
        (principalOccurrencePatchOpen y hy q).opensRange) ∧
    finitePrincipalAtlasRoutes U f y hy

/-- Actual covers and all comparison equations hold together at a bijective stage. -/
theorem exists_finitePrincipalAtlas_cover_comparison_stage :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (x : OccurrenceStage) (s : ∀ i, Finset (relationIdeal R Γ(X, (U i).1)))
      (t : AtlasPrincipalOverlap U → ι),
      (∀ j, (atlasPrincipalOpen U j).1 ≤ (U (t j)).1) →
      ∃ y : OccurrenceStage, ∃ _hxy : x ≤ y, s ≤ y.source ∧
        ∃ hy : ∀ i k, Function.Bijective (y.hom i k),
          (∀ j, (⨆ p : PrincipalOccurrencePatchTo (dst := D) j (t j),
            (principalOccurrencePatchOpen y hy p.1).opensRange) = ⊤) ∧
          finitePrincipalAtlasRoutes U f y hy := by
  intro _ _ _ _ x s t ht
  obtain ⟨z, hxz, hs, hz, hcz⟩ := exists_finitePrincipalAtlas_cover_stage U f x s t ht
  have H := exists_finitePrincipalAtlas_comparison_stage U f
  have H' := H z hz z.source
  obtain ⟨w, hzw, _, hw, he⟩ := H'
  refine ⟨w, hxz.trans hzw,
    fun i ↦ (hs i).trans (principalOccurrence_source_mono (dst := D) (a := AA) (b := BB)
      (f := fun i k ↦ (E i k).toAlgHom) hzw i), hw, hcz w hzw hw, he⟩

/-- Every required original geometric input and every comparison hold at one common stage. -/
theorem exists_finitePrincipalAtlas_coherent_stage :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (x : OccurrenceStage) (s : ∀ i, Finset (relationIdeal R Γ(X, (U i).1)))
      (t : AtlasPrincipalOverlap U → ι),
      (∀ j, (atlasPrincipalOpen U j).1 ≤ (U (t j)).1) →
      ∃ y : OccurrenceStage, ∃ _hxy : x ≤ y, s ≤ y.source ∧
        ∃ hy : ∀ i k, Function.Bijective (y.hom i k),
          finitePrincipalAtlasStageCoherent U f y hy t := by
  intro _ _ _ _ x s t ht
  obtain ⟨y, hxy, hs, _, hinc⟩ := exists_finitePrincipalAtlas_image_stage U f x s
  obtain ⟨z, hyz, _, hz, hc, he⟩ :=
    exists_finitePrincipalAtlas_cover_comparison_stage U f y y.source t ht
  refine ⟨z, hxy.trans hyz,
    fun i ↦ (hs i).trans (principalOccurrence_source_mono (dst := D) (a := AA) (b := BB)
      (f := fun i k ↦ (E i k).toAlgHom) hyz i), hz, hc, hinc z hyz hz, he⟩

end FLT.Mazur.Approximation

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasCoherentStage
public import FLT.Mazur.PrincipalOccurrenceAmbientCoverRefinement
public import FLT.Mazur.PrincipalOccurrenceCommonIdentities
/-!
# Diagonal coverage at coherent finite atlas stages

Actual original chart covers descend to finite ambient covers. The canonical
symmetric diagonal union therefore becomes the whole chart, while retaining
the target covers, image inclusions and exhaustive comparison equations.
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

omit [Finite ι] [LocallyOfFiniteType f] in
/-- The original occurrences cover the entire original affine spectrum. -/
theorem atlasPrincipal_original_ambient_cover (i : ι) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    (⨆ k : AtlasPrincipalOccurrence U i,
      (principalOccurrenceOriginalOpen (dst := D) (a := AA) (b := BB) E i k).opensRange) =
      ⊤ := by
  intro _ _
  let _ : IsOpenImmersion (U i).2.fromSpec := (U i).2.isOpenImmersion_fromSpec
  simp_rw [← atlasPrincipal_occurrence_preimage U f, ← atlasPrincipalSection_open]
  rw [← Scheme.Hom.preimage_iSup, atlasPrincipal_occurrences_cover]
  have h := Scheme.Hom.preimage_opensRange (U i).2.fromSpec
  rw [(U i).2.opensRange_fromSpec] at h
  exact h

/-- Every sufficiently refined diagonal common union is the whole finite ambient chart. -/
theorem exists_finitePrincipalAtlas_diagonal_stage :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (x : OccurrenceStage) (s : ∀ i, Finset (relationIdeal R Γ(X, (U i).1))),
      ∃ y : OccurrenceStage, ∃ _hxy : x ≤ y, s ≤ y.source ∧
        ∃ _hy : ∀ i k, Function.Bijective (y.hom i k),
          ∀ (z : OccurrenceStage) (_hyz : y ≤ z)
            (hz : ∀ i k, Function.Bijective (z.hom i k)) (i : ι),
            principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB) E z hz i i = ⊤ := by
  intro _ _ _ _ x s
  obtain ⟨y, hxy, hs, hy, hc⟩ :=
    exists_principalOccurrence_ambient_covers (dst := D) (a := AA) (b := BB) E x
      (atlasPrincipal_original_ambient_cover U f) s
  refine ⟨y, hxy, hs, hy, fun z hyz hz i ↦ ?_⟩
  rw [principalOccurrenceCommonUnion_diagonal]
  exact hc z hyz hz i

/-- Ambient diagonal coverage holds together with all previously constructed coherent data. -/
theorem exists_finitePrincipalAtlas_coherent_diagonal_stage :
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
          finitePrincipalAtlasStageCoherent U f y hy t ∧
            ∀ i, principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB) E y hy i i =
              ⊤ := by
  intro _ _ _ _ x s t ht
  obtain ⟨y, hxy, hs, _, hc⟩ := exists_finitePrincipalAtlas_diagonal_stage U f x s
  have H := exists_finitePrincipalAtlas_coherent_stage U f
  obtain ⟨z, hyz, _, hz, hcoh⟩ := H y y.source t ht
  exact ⟨z, hxy.trans hyz,
    fun i ↦ (hs i).trans (principalOccurrence_source_mono (dst := D) (a := AA) (b := BB)
      (f := fun i k ↦ (E i k).toAlgHom) hyz i), hz, hcoh, hc z hyz hz⟩

end FLT.Mazur.Approximation

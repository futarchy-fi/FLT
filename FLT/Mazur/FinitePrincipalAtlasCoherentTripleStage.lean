/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasTripleCoverStage
/-!
# Coherent atlas stages retaining all actual triple covers

Descend the finite triple covers first. Their persistence preserves them
while choosing whole diagonal unions and all remaining coherence equations.
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
  principalOccurrenceCommonUnion finitePrincipalAtlasStageCoherent
  numGenerators presentationMap atlasPrincipalTriplePatch FiniteRelationModel.relations

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

/-- A persistent triple cover is retained when choosing the remaining coherent stage data. -/
theorem exists_finitePrincipalAtlas_coherent_of_triple_cover :
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
      (∀ (z : OccurrenceStage) (_hxz : x ≤ z)
        (hz : ∀ i k, Function.Bijective (z.hom i k)) (j : AtlasPrincipalOverlap U)
        (n : AtlasPrincipalTripleIndex U j),
        (principalOccurrencePatchOpen z hz n.1).opensRange ≤
          ⨆ m, (principalOccurrencePatchOpen z hz
            (atlasPrincipalTriplePatch U j n m)).opensRange) →
      ∃ y : OccurrenceStage, ∃ _hxy : x ≤ y, s ≤ y.source ∧
        ∃ hy : ∀ i k, Function.Bijective (y.hom i k),
          finitePrincipalAtlasStageCoherent U f y hy t ∧
          (∀ i, principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB) E y hy i i =
            ⊤) ∧
          ∀ (j : AtlasPrincipalOverlap U) (n : AtlasPrincipalTripleIndex U j),
            (principalOccurrencePatchOpen y hy n.1).opensRange ≤
              ⨆ m, (principalOccurrencePatchOpen y hy
                (atlasPrincipalTriplePatch U j n m)).opensRange := by
  intro _ _ _ _ x s t ht hc
  have H := exists_finitePrincipalAtlas_coherent_diagonal_stage U f
  obtain ⟨z, hxz, hs, hz, hcoh, hdiag⟩ := H x s t ht
  exact ⟨z, hxz, hs, hz, hcoh, hdiag, hc z hxz hz⟩

/-- Triple-patch covers, whole diagonals and all atlas equations hold at one common stage. -/
theorem exists_finitePrincipalAtlas_coherent_triple_stage :
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
          (∀ i, principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB) E y hy i i =
            ⊤) ∧
          ∀ (j : AtlasPrincipalOverlap U) (n : AtlasPrincipalTripleIndex U j),
            (principalOccurrencePatchOpen y hy n.1).opensRange ≤
              ⨆ m, (principalOccurrencePatchOpen y hy
                (atlasPrincipalTriplePatch U j n m)).opensRange := by
  intro _ _ _ _ x s t ht
  have H₀ := exists_finitePrincipalAtlas_triple_cover_stage U f
  obtain ⟨y, hxy, _hs, _, hc⟩ := H₀ x s
  have H := exists_finitePrincipalAtlas_coherent_of_triple_cover U f
  have H' := H y s t ht
  have H'' := H' (fun z hyz hz j n ↦ hc z hyz hz j n)
  obtain ⟨z, hyz, hs, hz, hcoh, hdiag, htr⟩ := H''
  exact ⟨z, hxy.trans hyz,
    hs, hz, hcoh, hdiag, htr⟩

end FLT.Mazur.Approximation

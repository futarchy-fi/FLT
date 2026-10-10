/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasOriginalTripleCover
public import FLT.Mazur.PrincipalOccurrencePatchUnionRefinement
public import FLT.Mazur.FinitePrincipalAtlasDiagonalStage
/-!
# Simultaneous finite-stage covers of actual triple patches

All choices of an incident second chart and outer third-chart occurrence
form a finite family. Original geometry supplies every inclusion, so their
selected pair covers descend without extra finite-stage cover assumptions.
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

/-- All incident inner and outer routes needed for triple-intersection coverage. -/
abbrev AtlasPrincipalTripleIndex (j : AtlasPrincipalOverlap U) :=
  Σ p : PrincipalOccurrencePatch (dst := D) j, Σ t : ι,
    {k : AtlasPrincipalOccurrence U t // D t k = j} ×
      Σ r : ι, {l : AtlasPrincipalOccurrence U r // D r l = D p.1.val.1 p.2}

/-- The triple-route family is finite for a finite affine atlas. -/
instance atlasPrincipalTripleIndex_finite (j : AtlasPrincipalOverlap U) :
    Finite (AtlasPrincipalTripleIndex U j) := inferInstance

/-- Selected second-to-third pair overlaps as patches of the original inner overlap. -/
def atlasPrincipalTriplePatch (j : AtlasPrincipalOverlap U) (n : AtlasPrincipalTripleIndex U j)
    (m : atlasPrincipalPairs U n.2.1 n.2.2.2.1) : PrincipalOccurrencePatch (dst := D) j :=
  ⟨⟨⟨n.2.1, n.2.2.1.val⟩, n.2.2.1.property⟩, ⟨n.2.2.2.1, .inl m⟩⟩

/-- Every actual triple patch is covered by routes through the other pair on one finite tail. -/
theorem exists_finitePrincipalAtlas_triple_cover_stage :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (x : OccurrenceStage) (s : ∀ i, Finset (relationIdeal R Γ(X, (U i).1))),
      ∃ y : OccurrenceStage, ∃ _hxy : x ≤ y, s ≤ y.source ∧
        (∀ i k, Function.Bijective (y.hom i k)) ∧
        ∀ (z : OccurrenceStage) (_hyz : y ≤ z)
          (hz : ∀ i k, Function.Bijective (z.hom i k)) (j : AtlasPrincipalOverlap U)
          (n : AtlasPrincipalTripleIndex U j),
          (principalOccurrencePatchOpen z hz n.1).opensRange ≤
            ⨆ m, (principalOccurrencePatchOpen z hz
              (atlasPrincipalTriplePatch U j n m)).opensRange := by
  intro _ _ _ _ x s
  have H := exists_principalOccurrence_patch_union_inclusions (dst := D) (a := AA) (b := BB) E
  exact H x (fun j (n : AtlasPrincipalTripleIndex U j) ↦ n.1) (atlasPrincipalTriplePatch U)
    (fun j (n : AtlasPrincipalTripleIndex U j) ↦
      atlasPrincipal_original_triple_cover U f j n.1 n.2.1
      n.2.2.1.val n.2.2.1.property n.2.2.2.1 n.2.2.2.2.val n.2.2.2.2.property) s

end FLT.Mazur.Approximation

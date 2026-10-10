/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasCoherentTripleStage
public import FLT.Mazur.PrincipalOccurrenceCommonPatchRoutes
/-!
# Constructed triple routes at actual finite atlas stages

The simultaneous triple-cover theorem supplies the image conditions for
actual open immersions from every triple patch to its second-to-third union.
Their ambient factorization is retained together with coherent stage data.
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

/-- Actual triple-patch open immersions exist at a coherent finite stage with whole diagonals. -/
theorem exists_finitePrincipalAtlas_triple_routes_stage :
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
            ∃ g : principalOccurrencePatchScheme y n.1 ⟶
                (principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB)
                  E y hy n.2.1 n.2.2.2.1).toScheme,
              IsOpenImmersion g ∧
                g ≫ (principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB)
                  E y hy n.2.1 n.2.2.2.1).ι =
                  principalOccurrencePatchOpen y hy n.1 ≫
                    principalOccurrenceOpenAt (dst := D) (a := AA) (b := BB)
                      E y hy n.2.1 n.2.2.1.val n.2.2.1.property := by
  intro _ _ _ _ x s t ht
  have H := exists_finitePrincipalAtlas_coherent_triple_stage U f
  have H' := H x s t ht
  obtain ⟨y, hxy, hs, hy, hcoh, hdiag, hc⟩ := H'
  refine ⟨y, hxy, hs, hy, hcoh, hdiag, fun j n ↦ ?_⟩
  let l : atlasPrincipalPairs U n.2.1 n.2.2.2.1 → AtlasPrincipalOccurrence U n.2.1 :=
    fun m ↦ ⟨n.2.2.2.1, .inl m⟩
  let r : atlasPrincipalPairs U n.2.1 n.2.2.2.1 → AtlasPrincipalOccurrence U n.2.2.2.1 :=
    fun m ↦ ⟨n.2.1, .inr m⟩
  let g := principalOccurrenceCommonPatchRoute (dst := D) (a := AA) (b := BB) E y hy
    n.1 n.2.1 n.2.2.2.1 n.2.2.1.val n.2.2.1.property l r (fun _ ↦ rfl) (hc j n)
  refine ⟨g, ?_, principalOccurrenceCommonPatchRoute_fac (dst := D) (a := AA)
    (b := BB) E y hy n.1 n.2.1 n.2.2.2.1 n.2.2.1.val n.2.2.1.property
      l r (fun _ ↦ rfl) (hc j n)⟩
  exact principalOccurrenceCommonPatchRoute_isOpenImmersion (dst := D) (a := AA) (b := BB)
    E y hy n.1 n.2.1 n.2.2.2.1 n.2.2.1.val n.2.2.1.property l r (fun _ ↦ rfl) (hc j n)

end FLT.Mazur.Approximation

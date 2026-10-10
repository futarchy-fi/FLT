/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasTripleComparison
public import FLT.Mazur.PrincipalOccurrenceCommonTripleLift
/-!
# Full ambient triple routes at actual finite atlas stages

Original triple-cover geometry and exhaustive comparisons produce routes
on the entire pullback of any two canonical unions. Both ambient
factorizations hold on that full domain.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv principalOccurrenceLocalComparisonLeft
  principalOccurrenceLocalComparisonRight principalOccurrenceCrossEquationTransport
  principalOccurrencePatchOpen principalOccurrenceCrossOuterLeft principalOccurrenceCrossOuterRight
  principalOccurrenceOpenAt relationIdeal chartAlgebra principalRepresentative
  principalOccurrenceStagePreorder
  principalOccurrenceCommonUnion

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

/-- Full ambient triple routes exist at one coherent stage above any relation bound. -/
theorem exists_finitePrincipalAtlas_ambient_triple_stage :
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
          ∃ he : finitePrincipalAtlasRoutes U f y hy,
          finitePrincipalAtlasStageCoherent U f y hy t ∧
          (∀ i, principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB) E y hy i i =
            ⊤) ∧
          ∀ i t r : ι,
            ∃ g : pullback
                (principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB) E y hy i t).ι
                (principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB) E y hy i r).ι ⟶
                (principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB)
                  E y hy t r).toScheme,
              IsOpenImmersion g ∧
                g ≫ (principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB)
                    E y hy t r).ι =
                  pullback.fst _ _ ≫
                    (principalOccurrenceCommonUnionIso (dst := D) (a := AA) (b := BB)
                      E y hy he i t).hom ≫
                    (principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB)
                      E y hy t i).ι ∧
                g ≫ (principalOccurrenceCommonUnionIso (dst := D) (a := AA) (b := BB)
                    E y hy he t r).hom ≫
                    (principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB)
                      E y hy r t).ι =
                  pullback.snd _ _ ≫
                    (principalOccurrenceCommonUnionIso (dst := D) (a := AA) (b := BB)
                      E y hy he i r).hom ≫
                    (principalOccurrenceCommonUnion (dst := D) (a := AA) (b := BB)
                      E y hy r i).ι := by
  intro _ _ _ _ x s t ht
  have H := exists_finitePrincipalAtlas_triple_comparison_stage U f
  obtain ⟨y, hxy, hs, hy, he, hcoh, hdiag, htr⟩ := H x s t ht
  refine ⟨y, hxy, hs, hy, he, hcoh, hdiag, fun i t r ↦ ?_⟩
  apply exists_principalOccurrenceCommonTriple_route (dst := D) (a := AA) (b := BB)
    E y hy he i t r
  intro p q
  let n : AtlasPrincipalTripleIndex U p.1 :=
    ⟨principalOccurrenceCommonDoublePatch i t r p q, t, p.2.2,
      r, ⟨q.2.2.val, q.2.2.property.trans q.2.1.property.symm⟩⟩
  obtain ⟨g, _, hg, hg'⟩ := htr p.1 n
  exact ⟨g, hg, hg'⟩

end FLT.Mazur.Approximation

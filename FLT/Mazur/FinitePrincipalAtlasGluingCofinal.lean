/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasAmbientTripleStage
public import FLT.Mazur.PrincipalOccurrenceGluingIndex
public import FLT.Mazur.PrincipalOccurrenceGluedTransitions
/-!
# Cofinal gluable stages of an actual finite principal atlas

The original atlas constructs members of the gluable-stage subtype above
any occurrence stage and prescribed ambient relation bounds.
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

/-- Gluable finite stages are cofinal, retaining all specified source relation bounds. -/
theorem exists_finitePrincipalAtlas_gluingStage :
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
      ∃ y : PrincipalOccurrenceGluingStage (dst := D) (a := AA) (b := BB) E,
        x ≤ y.val ∧ s ≤ y.val.source := by
  intro _ _ _ _ x s t ht
  obtain ⟨y, hxy, hs, hy, he, _hc, hd, hr⟩ :=
    exists_finitePrincipalAtlas_ambient_triple_stage U f x s t ht
  exact ⟨⟨y, hy, he, hd, hr⟩, hxy, hs⟩

/-- The gluable-stage index of the original finite atlas is filtered. -/
theorem finitePrincipalAtlas_gluingStage_filtered :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    IsFiltered (PrincipalOccurrenceGluingStage (dst := D) (a := AA) (b := BB) E) := by
  intro _ _ _ _
  apply principalOccurrenceGluingStage_filtered
  intro x
  obtain ⟨y, hxy, _hs⟩ := exists_finitePrincipalAtlas_gluingStage U f x (fun _ ↦ ∅)
    (fun j ↦ j.1) (atlasPrincipalOpen_le_left U)
  exact ⟨y, hxy⟩

/-- The nonaffine inverse system constructed from the original finite atlas. -/
def finitePrincipalAtlasGluedDiagram :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    (PrincipalOccurrenceGluingStage (dst := D) (a := AA) (b := BB) E)ᵒᵖ ⥤ Scheme.{u} := by
  intro _ _ _ _
  exact principalOccurrenceGluedDiagram (dst := D) (a := AA) (b := BB) E

end FLT.Mazur.Approximation

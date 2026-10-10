/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasAffineLimit
public import FLT.Mazur.CofinalUpperLimit
/-!
# Upper-stage affine limit recovery for a finite atlas

The geometric stage index is nonempty and directed. Its affine chart limits
therefore remain limits above any prescribed gluable stage.
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
  PrincipalOccurrenceGluingStage (dst := D) (a := AA) (b := BB) E

/-- Actual gluable atlas stages have common refinements. -/
theorem finitePrincipalAtlas_gluingStage_directed :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    IsDirectedOrder OccurrenceStage := by
  intro _ _ _ _
  let _ := finitePrincipalAtlas_gluingStage_filtered U f
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨z, a, b, _⟩ := IsFilteredOrEmpty.cocone_objs x y
  exact ⟨z, leOfHom a, leOfHom b⟩

/-- There is at least one actual gluable atlas stage. -/
theorem finitePrincipalAtlas_gluingStage_nonempty :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    Nonempty OccurrenceStage := by
  intro _ _ _ _
  let _ := finitePrincipalAtlas_gluingStage_filtered U f
  exact IsFiltered.nonempty

/-- Every original affine chart is recovered above any chosen geometric stage. -/
def finitePrincipalAtlasAffineUpperIsLimit (i : ι) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ x : OccurrenceStage,
      IsLimit ((principalOccurrenceGluingAffineCone (dst := D) (a := AA) (b := BB) E i).whisker
        (upperStageInclusion x).op) := by
  intro _ _ _ _ x
  let _ := finitePrincipalAtlas_gluingStage_directed U f
  exact upperStageIsLimit x (finitePrincipalAtlasAffineIsLimit U f i)

end FLT.Mazur.Approximation

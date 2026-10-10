/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasGluingCofinal
public import FLT.Mazur.PrincipalOccurrenceGluingAffineLimit
/-!
# Limit recovery of actual original affine atlas charts

The finite-atlas cofinality construction supplies the hypotheses of the
affine limit over gluable stages, with the literal ambient projections.
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

/-- Each original affine atlas chart is the limit over the actual gluable-stage index. -/
def finitePrincipalAtlasAffineIsLimit (i : ι) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    IsLimit (principalOccurrenceGluingAffineCone (dst := D) (a := AA) (b := BB) E i) := by
  intro _ _ _ _
  apply principalOccurrenceGluingAffineIsLimit (dst := D) (a := AA) (b := BB) E
  intro x
  obtain ⟨y, hxy, _hs⟩ := exists_finitePrincipalAtlas_gluingStage U f x (fun _ ↦ ∅)
    (fun j ↦ j.1) (atlasPrincipalOpen_le_left U)
  exact ⟨y, hxy⟩

omit [Finite ι] in
/-- The affine limit legs are precisely the original ambient chart projections. -/
theorem finitePrincipalAtlasAffineCone_app (i : ι) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ x : PrincipalOccurrenceGluingStage (dst := D) (a := AA) (b := BB) E,
      (principalOccurrenceGluingAffineCone (dst := D) (a := AA) (b := BB) E i).π.app (.op x) =
        principalOccurrenceAmbientProjection (dst := D) (a := AA) (b := BB) E x.val i := by
  intro _ _ _ _ x
  rfl

end FLT.Mazur.Approximation

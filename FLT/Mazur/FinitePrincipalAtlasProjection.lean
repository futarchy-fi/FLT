/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasCommonCover
public import FLT.Mazur.PrincipalOccurrenceGluedIncidence

/-!
# The original scheme maps to every glued finite stage

A genuine covering hypothesis on the original affine family gives an
open cover. Literal common-overlap compatibility glues its chart projections.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv chartAlgebra principalRepresentative

universe u v

variable {R : CommRingCat.{u}} {X : Scheme.{u}} [QuasiSeparatedSpace X]
  {ι : Type v} [Finite ι] (U : ι → X.affineOpens) (f : X ⟶ Spec R)
  [LocallyOfFiniteType f]

local notation "D" => atlasPrincipalDestination U
local notation "AA" => atlasPrincipalSection U
set_option quotPrecheck false in
local notation "BB" => fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1))
local notation "E" => atlasPrincipalEquiv U f

local notation "OccurrenceStage" => PrincipalOccurrenceGluingStage (dst := D) (a := AA) (b := BB) E

/-- A genuine finite atlas cover, with the same shrunk labels as the glued stages. -/
def finitePrincipalAtlasOriginalCover
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) : X.OpenCover.{u} :=
  (Scheme.AffineOpenCover.ofIsOpenCover (fun i : Shrink.{u} ι ↦ (U ((equivShrink.{u} ι).symm i)).1)
    (by
      change (⨆ i : Shrink.{u} ι, (U ((equivShrink.{u} ι).symm i)).1) = ⊤
      exact ((equivShrink.{u} ι).symm.surjective.iSup_comp (fun i ↦ (U i).1)).trans hU)
    (fun i ↦ (U ((equivShrink.{u} ι).symm i)).2)).openCover

/-- Original chart projections agree on their actual full intersections. -/
theorem finitePrincipalAtlasProjection_compatible :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (x : OccurrenceStage) (i t : Shrink.{u} ι),
      pullback.fst (U ((equivShrink.{u} ι).symm i)).2.fromSpec
          (U ((equivShrink.{u} ι).symm t)).2.fromSpec ≫
          principalOccurrenceOriginalGluedChart (dst := D) (a := AA) (b := BB) E x i =
        pullback.snd (U ((equivShrink.{u} ι).symm i)).2.fromSpec
          (U ((equivShrink.{u} ι).symm t)).2.fromSpec ≫
          principalOccurrenceOriginalGluedChart (dst := D) (a := AA) (b := BB) E x t := by
  intro _ _ _ _ x i t
  exact atlasPrincipalOriginalCommon_compatible U f
    ((equivShrink.{u} ι).symm i) ((equivShrink.{u} ι).symm t) _ _
    (principalOccurrenceOriginalGluedChart_incidence (dst := D) (a := AA) (b := BB) E x i t)

/-- The original scheme projects to each constructed glued stage. -/
def finitePrincipalAtlasProjection
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ x : OccurrenceStage,
      X ⟶ (principalOccurrenceStageGlueData (dst := D) (a := AA) (b := BB) E x).glued := by
  intro _ _ _ _ x
  exact (finitePrincipalAtlasOriginalCover U hU).glueMorphisms
    (principalOccurrenceOriginalGluedChart (dst := D) (a := AA) (b := BB) E x)
    (finitePrincipalAtlasProjection_compatible U f x)

/-- Every projection recovers the prescribed map from each original affine chart. -/
@[reassoc] theorem finitePrincipalAtlasProjection_chart
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (x : OccurrenceStage) (i : Shrink.{u} ι),
      (U ((equivShrink.{u} ι).symm i)).2.fromSpec ≫ finitePrincipalAtlasProjection U f hU x =
        principalOccurrenceOriginalGluedChart (dst := D) (a := AA) (b := BB) E x i := by
  intro _ _ _ _ x i
  exact (finitePrincipalAtlasOriginalCover U hU).ι_glueMorphisms
    (principalOccurrenceOriginalGluedChart (dst := D) (a := AA) (b := BB) E x)
    (finitePrincipalAtlasProjection_compatible U f x) i

end FLT.Mazur.Approximation

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasProjectionCartesian
public import FLT.Mazur.FiniteTypeAffineApproximation

/-!
# Closed immersion projections to glued finite stages

The cartesian whole-chart squares identify each restriction with a
surjective finite-relation spectrum map. Closed immersion descent gives
a monomorphism for every global original-scheme projection.
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

local notation "AP" => principalOccurrenceAmbientProjection (dst := D) (a := AA) (b := BB) E

/-- Every original-scheme projection is a closed immersion. -/
theorem finitePrincipalAtlasProjection_isClosedImmersion
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ x : OccurrenceStage, IsClosedImmersion (finitePrincipalAtlasProjection U f hU x) := by
  intro _ _ _ _ x
  let G := principalOccurrenceStageGlueData (dst := D) (a := AA) (b := BB) E x
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) G.openCover
  intro i
  have h := finitePrincipalAtlasProjection_isPullback U f hU x i
  let _ : IsClosedImmersion (AP x.val ((equivShrink.{u} ι).symm i)) :=
    IsClosedImmersion.spec_of_surjective _ (stageMap_surjective _ _ _)
  change IsClosedImmersion (pullback.snd (finitePrincipalAtlasProjection U f hU x)
    ((principalOccurrenceStageGlueData (dst := D) (a := AA) (b := BB) E x).ι i))
  exact (congrArg (fun k ↦ IsClosedImmersion k) h.flip.isoPullback_inv_snd).mp
    (inferInstanceAs (IsClosedImmersion (h.flip.isoPullback.inv ≫ _)))

/-- Global original projections can be cancelled when comparing glued lifts. -/
theorem finitePrincipalAtlasProjection_mono
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ x : OccurrenceStage, Mono (finitePrincipalAtlasProjection U f hU x) := by
  intro _ _ _ _ x
  let _ := finitePrincipalAtlasProjection_isClosedImmersion U f hU x
  infer_instance

end FLT.Mazur.Approximation

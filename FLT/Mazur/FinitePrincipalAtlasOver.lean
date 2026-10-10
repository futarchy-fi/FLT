/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasLimit
public import FLT.Mazur.PrincipalOccurrenceGluedStructure
public import FLT.Mazur.BaseAdicReesSpace

/-!
# Original atlas projections retain the original structure morphism

The global projection to every constructed finite stage is a morphism
over the original affine base. This uses the original chart scalar maps,
not a newly selected or abstractly isomorphic base structure.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv principalRepresentative

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

/-- Composing any original-scheme projection with the stage structure map recovers `f`. -/
@[reassoc] theorem finitePrincipalAtlasProjection_over
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ x : OccurrenceStage,
      finitePrincipalAtlasProjection U f hU x ≫
        principalOccurrenceGluedStructure (dst := D) (a := AA) (b := BB) E x = f := by
  intro _ _ _ _ x
  apply (finitePrincipalAtlasOriginalCover U hU).hom_ext
  intro k
  change Shrink.{u} ι at k
  change (U ((equivShrink.{u} ι).symm k)).2.fromSpec ≫ _ =
    (U ((equivShrink.{u} ι).symm k)).2.fromSpec ≫ f
  rw [finitePrincipalAtlasProjection_chart_assoc]
  unfold principalOccurrenceOriginalGluedChart
  refine (Category.assoc _ _ _).trans ((congrArg
    (fun z ↦ principalOccurrenceAmbientProjection (dst := D) (a := AA) (b := BB) E
      x.val ((equivShrink.{u} ι).symm k) ≫ z)
    (principalOccurrenceGluedStructure_chart (dst := D) (a := AA) (b := BB) E x k)).trans ?_)
  refine (affineProjection_over R Γ(X, (U ((equivShrink.{u} ι).symm k)).1)
    (x.val.source ((equivShrink.{u} ι).symm k))).trans ?_
  exact chartScalars_spec f (U ((equivShrink.{u} ι).symm k))

end FLT.Mazur.Approximation

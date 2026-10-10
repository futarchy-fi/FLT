/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasCone
public import FLT.Mazur.FinitePrincipalAtlasProjectionClosed
public import FLT.Mazur.FinitePrincipalAtlasUpperLimit
public import FLT.Mazur.PrincipalOccurrenceChartDiagram
public import FLT.Mazur.CartesianUpperCone
public import FLT.Mazur.SchemeConeGluing

/-!
# The original scheme is the limit of its glued finite stages

Pull back the chart cover at one gluable stage to an arbitrary test cone.
The cartesian chart transitions give cones above that stage; the affine
limits lift them into the original charts. Projection monicity makes these
lifts agree on overlaps, so they glue into the unique global lift.
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

/-- Global limit recovery using a prescribed stage to cover each test cone. -/
def finitePrincipalAtlasIsLimitAtStage
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ _ : OccurrenceStage, IsLimit (finitePrincipalAtlasCone U f hU) := by
  intro _ _ _ _ x
  let _ := finitePrincipalAtlas_gluingStage_directed U f
  let c := finitePrincipalAtlasCone U f hU
  let _ : Mono (c.π.app (.op x)) := finitePrincipalAtlasProjection_mono U f hU x
  let V₀ := (principalOccurrenceStageGlueData (dst := D) (a := AA) (b := BB) E x).openCover
  let V (s : Cone (finitePrincipalAtlasGluedDiagram U f)) := V₀.pullback₁ (s.π.app (.op x))
  let η (k : Shrink.{u} ι) :=
    principalOccurrenceChartInclusion (dst := D) (a := AA) (b := BB) E k
  let _ (k : Shrink.{u} ι) (y : OccurrenceStageᵒᵖ) :
      IsOpenImmersion ((η k).app y) :=
    principalOccurrenceChartInclusion_isOpenImmersion (dst := D) (a := AA) (b := BB) E k y
  let _ (k : Shrink.{u} ι) (y : OccurrenceStageᵒᵖ) : Mono ((η k).app y) := inferInstance
  let H (k : Shrink.{u} ι) (y : Set.Ici x) :=
    principalOccurrenceChartInclusion_isPullback (dst := D) (a := AA) (b := BB) E k
      (homOfLE y.property).op
  let q (s : Cone (finitePrincipalAtlasGluedDiagram U f)) (k : Shrink.{u} ι) :=
    V₀.pullbackHom (s.π.app (.op x)) k
  have hq (s : Cone (finitePrincipalAtlasGluedDiagram U f)) (k : Shrink.{u} ι) :
      q s k ≫ (η k).app (.op x) = (V s).f k ≫ s.π.app (.op x) :=
    V₀.pullbackHom_map (s.π.app (.op x)) k
  let L (s : Cone (finitePrincipalAtlasGluedDiagram U f)) (k : Shrink.{u} ι) :=
    cartesianUpperLift (η k) x (H k) s ((V s).f k) (q s k) (hq s k)
      (finitePrincipalAtlasAffineIsLimit U f ((equivShrink.{u} ι).symm k))
  refine schemeConeIsLimitOfLocalLifts c x V
    (fun s k ↦ L s k ≫ (U ((equivShrink.{u} ι).symm k)).2.fromSpec) ?_
  intro s k y
  change Shrink.{u} ι at k
  have hh := cartesianUpperLift_app (η k) x (H k) s ((V s).f k) (q s k) (hq s k)
    (finitePrincipalAtlasAffineIsLimit U f ((equivShrink.{u} ι).symm k)) y
  change (L s k ≫ (U ((equivShrink.{u} ι).symm k)).2.fromSpec) ≫
    finitePrincipalAtlasProjection U f hU y.val = _
  refine (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦ L s k ≫ z) (finitePrincipalAtlasProjection_chart U f hU y.val k)).trans ?_)
  unfold principalOccurrenceOriginalGluedChart
  exact hh

/-- The actual original scheme is the inverse limit of its constructed finite stages. -/
def finitePrincipalAtlasIsLimit
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    IsLimit (finitePrincipalAtlasCone U f hU) := by
  intro _ _ _ _
  exact finitePrincipalAtlasIsLimitAtStage U f hU
    (Classical.choice (finitePrincipalAtlas_gluingStage_nonempty U f))

end FLT.Mazur.Approximation

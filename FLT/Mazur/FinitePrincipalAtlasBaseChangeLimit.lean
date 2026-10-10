/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasOver
public import FLT.Mazur.PrincipalOccurrenceGluedStructure
public import FLT.Mazur.BaseAdicReesSpace
public import FLT.Mazur.SchemeClosedBaseChange

/-!
# Base change of the actual occurrence limit

The original scheme's fiber, including a residue-field fiber, is the limit
of the fibers of its finite occurrence stages. The fiber projections are
closed immersions and the transitions remain closed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

/-- The actual finite occurrence diagram after a fixed base change. -/
def finitePrincipalAtlasBaseChangeDiagram {Y : Scheme.{u}} (q : Y ⟶ Spec R) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    OccurrenceStageᵒᵖ ⥤ Scheme.{u} := by
  intro _ _ _ _
  exact schemeBaseChangeDiagram
    (principalOccurrenceGluedToBase (dst := D) (a := AA) (b := BB) E) q

/-- The original base change supplies the cone to the finite occurrence fibers. -/
def finitePrincipalAtlasBaseChangeCone
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1))
    {Y : Scheme.{u}} (q : Y ⟶ Spec R) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    Cone (finitePrincipalAtlasBaseChangeDiagram U f q) := by
  intro _ _ _ _
  exact schemeBaseChangeCone
    (principalOccurrenceGluedToBase (dst := D) (a := AA) (b := BB) E) q
    (finitePrincipalAtlasCone U f hU) f (fun x ↦ finitePrincipalAtlasProjection_over U f hU x.unop)

/-- The original fiber is the inverse limit of the actual finite-stage fibers. -/
def finitePrincipalAtlasBaseChangeIsLimit
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1))
    {Y : Scheme.{u}} (q : Y ⟶ Spec R) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    IsLimit (finitePrincipalAtlasBaseChangeCone U f hU q) := by
  intro _ _ _ _
  let _ := finitePrincipalAtlas_gluingStage_filtered U f
  let _ := IsCofiltered.isConnected (OccurrenceStageᵒᵖ)
  exact schemeBaseChangeIsLimit (I := OccurrenceStageᵒᵖ)
    (principalOccurrenceGluedToBase (dst := D) (a := AA) (b := BB) E) q
    (finitePrincipalAtlasCone U f hU) f
    (fun x ↦ finitePrincipalAtlasProjection_over U f hU x.unop)
    (finitePrincipalAtlasIsLimit U f hU)

/-- The recovery projections on fibers are closed immersions. -/
theorem finitePrincipalAtlasBaseChangeCone_closed
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1))
    {Y : Scheme.{u}} (q : Y ⟶ Spec R) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ x : OccurrenceStage,
      IsClosedImmersion ((finitePrincipalAtlasBaseChangeCone U f hU q).π.app (.op x)) := by
  intro _ _ _ _ x
  let c := finitePrincipalAtlasCone U f hU
  let _ : IsClosedImmersion (c.π.app (.op x)) :=
    finitePrincipalAtlasProjection_isClosedImmersion U f hU x
  exact schemeBaseChangeCone_app_isClosedImmersion
    (principalOccurrenceGluedToBase (dst := D) (a := AA) (b := BB) E) q c f
    (fun y ↦ finitePrincipalAtlasProjection_over U f hU y.unop) (.op x)

end FLT.Mazur.Approximation

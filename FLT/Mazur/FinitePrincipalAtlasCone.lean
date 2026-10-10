/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasProjection
public import FLT.Mazur.FinitePrincipalAtlasGluingCofinal

/-!
# The original scheme cone over the nonaffine finite-stage diagram

Chartwise compatibility with refinement gives the naturality of the global
projections. Thus the original covered scheme supplies a genuine cone.
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

/-- Global projections commute with every refinement of gluable stages. -/
@[reassoc] theorem finitePrincipalAtlasProjection_transition
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ (x y : OccurrenceStage) (hxy : x ≤ y),
      finitePrincipalAtlasProjection U f hU y ≫
          principalOccurrenceGluedTransition (dst := D) (a := AA) (b := BB) E x y hxy =
        finitePrincipalAtlasProjection U f hU x := by
  intro _ _ _ _ x y hxy
  apply (finitePrincipalAtlasOriginalCover U hU).hom_ext
  intro i
  change Shrink.{u} ι at i
  change (U ((equivShrink.{u} ι).symm i)).2.fromSpec ≫ _ =
    (U ((equivShrink.{u} ι).symm i)).2.fromSpec ≫ _
  rw [finitePrincipalAtlasProjection_chart_assoc, finitePrincipalAtlasProjection_chart,
    principalOccurrenceOriginalGluedChart_transition]

/-- The original covered scheme is the point of a compatible nonaffine inverse-system cone. -/
def finitePrincipalAtlasCone
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    Cone (finitePrincipalAtlasGluedDiagram U f) := by
  intro _ _ _ _
  exact
    { pt := X
      π :=
        { app := fun x ↦ finitePrincipalAtlasProjection U f hU x.unop
          naturality := fun x y h ↦ by
            exact (Category.id_comp _).trans
              (finitePrincipalAtlasProjection_transition U f hU y.unop x.unop
                (leOfHom h.unop)).symm } }

/-- Cone components are exactly the glued original ambient projections. -/
theorem finitePrincipalAtlasCone_app
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ x : OccurrenceStage,
      (finitePrincipalAtlasCone U f hU).π.app (.op x) =
        finitePrincipalAtlasProjection U f hU x := by
  intro _ _ _ _ x
  rfl

end FLT.Mazur.Approximation

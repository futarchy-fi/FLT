/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasLimit
public import FLT.Mazur.PrincipalOccurrenceChartOpens
public import FLT.Mazur.PrincipalOccurrenceGluedQuasiSeparated
public import FLT.Mazur.FinitePrincipalAtlasSeparated
public import FLT.Mazur.FinitePrincipalAtlasOver
public import FLT.Mazur.PrincipalOccurrenceGluedFiniteness
public import FLT.Mazur.ProperClosedLimitDescent

/-!
# Proper finite stages over the original affine base

Properness of the original map descends to a constructed occurrence stage.
The separated refinement comes first; the immersed proper cover argument
then gives universal closedness without finite presentation of the limit.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv principalRepresentative

universe u

variable {R : CommRingCat.{u}} {X : Scheme.{u}} [QuasiSeparatedSpace X]
  {ι : Type u} [Finite ι] (U : ι → X.affineOpens) (f : X ⟶ Spec R)
  [IsProper f]

local notation "D" => atlasPrincipalDestination U
local notation "AA" => atlasPrincipalSection U
set_option quotPrecheck false in
local notation "BB" => fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1))
local notation "E" => atlasPrincipalEquiv U f

local notation "OccurrenceStage" => PrincipalOccurrenceGluingStage (dst := D) (a := AA) (b := BB) E

/-- Every geometric stage has a proper refinement over the original affine base. -/
theorem exists_finitePrincipalAtlas_isProper
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ x : OccurrenceStage, ∃ y : OccurrenceStage, x ≤ y ∧
      IsProper (principalOccurrenceGluedStructure (dst := D) (a := AA) (b := BB) E y) := by
  have hf : IsProper f := inferInstance
  intro _ _ _ _ x
  obtain ⟨y, hxy, hy⟩ := exists_finitePrincipalAtlas_isSeparated U f hU x
  let _ := finitePrincipalAtlas_gluingStage_filtered U f
  let F := finitePrincipalAtlasGluedDiagram U f
  let c := finitePrincipalAtlasCone U f hU
  let g : F.obj (.op y) ⟶ Spec R :=
    principalOccurrenceGluedStructure (dst := D) (a := AA) (b := BB) E y
  let _ : LocallyOfFinitePresentation g :=
    principalOccurrenceGluedStructure_locallyOfFinitePresentation
      (dst := D) (a := AA) (b := BB) E y
  let _ : IsSeparated g := hy
  let _ : QuasiCompact g :=
    principalOccurrenceGluedStructure_quasiCompact (dst := D) (a := AA) (b := BB) E y
  let _ {s t : OccurrenceStageᵒᵖ} (h : s ⟶ t) : IsClosedImmersion (F.map h) :=
    principalOccurrenceGluedDiagram_map_isClosedImmersion (dst := D) (a := AA) (b := BB) E h
  let _ : IsClosedImmersion (c.π.app (.op y)) :=
    finitePrincipalAtlasProjection_isClosedImmersion U f hU y
  have he : c.π.app (.op y) ≫ g = f := finitePrincipalAtlasProjection_over U f hU y
  let _ : IsProper (c.π.app (.op y) ≫ g) := he.symm ▸ hf
  obtain ⟨z, h, hz⟩ := exists_isProper_of_closed_limit F c
    (finitePrincipalAtlasIsLimit U f hU) (.op y) g
  refine ⟨z.unop, hxy.trans (leOfHom h.unop), ?_⟩
  exact (congrArg (fun t ↦ IsProper t)
    (principalOccurrenceGluedTransition_over (dst := D) (a := AA) (b := BB) E
      y z.unop (leOfHom h.unop))).mp hz

end FLT.Mazur.Approximation

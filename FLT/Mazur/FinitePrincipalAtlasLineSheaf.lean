/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasProper
public import FLT.Mazur.TrivializedLineSheafLimitDescent

/-!
# A specified line sheaf at a proper occurrence stage

Choose an atlas trivializing the line sheaf. Its actual occurrence system
has proper refinements carrying a line sheaf whose closed-projection pullback
recovers the specified original sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel FLT.Mazur.FCurve

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv principalRepresentative

universe u

variable {R : CommRingCat.{u}} {X : Scheme.{u}} [QuasiSeparatedSpace X]
  {ι : Type u} [Finite ι] (U : ι → X.affineOpens) (f : X ⟶ Spec R) [IsProper f]

local notation "D" => atlasPrincipalDestination U
local notation "AA" => atlasPrincipalSection U
set_option quotPrecheck false in
local notation "BB" => fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1))
local notation "E" => atlasPrincipalEquiv U f
local notation "OccurrenceStage" => PrincipalOccurrenceGluingStage (dst := D) (a := AA) (b := BB) E
local notation "V" => principalOccurrenceGluedChartOpen (dst := D) (a := AA) (b := BB) E

/-- Proper occurrence refinements carry the specified line sheaf with exact pullback recovery. -/
theorem exists_finitePrincipalAtlas_lineSheaf
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) (L : X.Modules)
    (e : ∀ i, Nonempty (L.restrict (U i).1.ι ≅ structureModule (U i).1.toScheme)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ x : OccurrenceStage, ∃ y : OccurrenceStage, x ≤ y ∧
      IsProper (principalOccurrenceGluedStructure (dst := D) (a := AA) (b := BB) E y) ∧
      ∃ M : ((finitePrincipalAtlasGluedDiagram U f).obj (.op y)).Modules,
        LocallyFreeRankOne M ∧ Nonempty
          ((Scheme.Modules.pullback (finitePrincipalAtlasProjection U f hU y)).obj M ≅ L) := by
  intro _ _ _ _ x
  obtain ⟨y, hxy, hy⟩ := exists_finitePrincipalAtlas_isProper U f hU x
  let _ := finitePrincipalAtlas_gluingStage_filtered U f
  let F := finitePrincipalAtlasGluedDiagram U f
  let c := finitePrincipalAtlasCone U f hU
  let gy : F.obj (.op y) ⟶ Spec R :=
    principalOccurrenceGluedStructure (dst := D) (a := AA) (b := BB) E y
  let _ : IsProper gy := hy
  let _ : (F.obj (.op y)).IsSeparated := ⟨by
    simpa only [terminal.comp_from] using
      (inferInstance : IsSeparated (gy ≫ terminal.from (Spec R)))⟩
  let _ (s : OccurrenceStageᵒᵖ) : QuasiSeparatedSpace (F.obj s) :=
    principalOccurrenceStageGlueData_quasiSeparatedSpace (dst := D) (a := AA) (b := BB) E s.unop
  let _ {s t : OccurrenceStageᵒᵖ} (h : s ⟶ t) : IsAffineHom (F.map h) :=
    principalOccurrenceGluedDiagram_map_isAffineHom (dst := D) (a := AA) (b := BB) E h
  let VV : Shrink.{u} ι → (F.obj (.op y)).Opens := V y
  have hcover : iSup (VV) = ⊤ :=
    (principalOccurrenceStageGlueData (dst := D) (a := AA) (b := BB) E y).openCover
      |>.isOpenCover_opensRange
  have hcompact s : IsCompact (finiteIntersectionOpen (VV) s : Set (F.obj (.op y))) := by
    have ha : IsAffineOpen (finiteIntersectionOpen (VV) s) :=
      finiteIntersectionSchemeDiagram_isAffine (VV)
        (principalOccurrenceGluedChartOpen_isAffine (dst := D) (a := AA) (b := BB) E y) (.op s)
    exact ha.isCompact
  let q : X ⟶ F.obj (.op y) := c.π.app (.op y)
  have he i : Nonempty (L.restrict (q ⁻¹ᵁ VV i).ι ≅
      structureModule (q ⁻¹ᵁ VV i).toScheme) := by
    have hpre : q ⁻¹ᵁ VV i = (U ((equivShrink.{u} ι).symm i)).1 :=
      TopologicalSpace.Opens.ext ((finitePrincipalAtlasProjection_preimage U f hU y i).trans
        (congrArg SetLike.coe (U ((equivShrink.{u} ι).symm i)).2.opensRange_fromSpec))
    rw [hpre]
    exact e _
  obtain ⟨r, M, hM, hrec⟩ := exists_trivializedLineSheaf_of_limit F c
    (finitePrincipalAtlasIsLimit U f hU) (.op y) (VV) hcover hcompact L he
  have hyr : y ≤ r.left.unop := leOfHom r.hom.unop
  let _ : IsClosedImmersion (F.map r.hom) :=
    principalOccurrenceGluedDiagram_map_isClosedImmersion (dst := D) (a := AA) (b := BB) E r.hom
  have hr : IsProper (F.map r.hom ≫ gy) := inferInstance
  refine ⟨r.left.unop, hxy.trans hyr, ?_, M, hM, hrec⟩
  exact (congrArg (fun t ↦ IsProper t)
    (principalOccurrenceGluedTransition_over (dst := D) (a := AA) (b := BB) E
      y r.left.unop hyr)).mp hr

end FLT.Mazur.Approximation

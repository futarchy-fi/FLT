/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasLimit
public import FLT.Mazur.PrincipalOccurrenceChartOpens
public import FLT.Mazur.PrincipalOccurrenceGluedQuasiSeparated
public import FLT.Mazur.CartesianAtlasAffineIntersections

/-!
# Affine intersections at a finite stage of the original atlas

When the original structure morphism is separated, every chosen geometric
stage has a refinement whose actual chart intersections are all affine.
The index and transitions are the previously constructed occurrence stages.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicRees FLT.Mazur.FiniteTypeRelationModel

namespace FLT.Mazur.Approximation

attribute [local irreducible] atlasPrincipalEquiv principalRepresentative

universe u

variable {R : CommRingCat.{u}} {X : Scheme.{u}} [QuasiSeparatedSpace X]
  {ι : Type u} [Finite ι] (U : ι → X.affineOpens) (f : X ⟶ Spec R)
  [LocallyOfFiniteType f]

local notation "D" => atlasPrincipalDestination U
local notation "AA" => atlasPrincipalSection U
set_option quotPrecheck false in
local notation "BB" => fun j ↦ (1 : Γ(X, (atlasPrincipalOpen U j).1))
local notation "E" => atlasPrincipalEquiv U f

local notation "OccurrenceStage" => PrincipalOccurrenceGluingStage (dst := D) (a := AA) (b := BB) E

local notation "V" => principalOccurrenceGluedChartOpen (dst := D) (a := AA) (b := BB) E

/-- Separatedness of the original map gives affine chart intersections on a refinement. -/
theorem exists_finitePrincipalAtlas_affine_intersections [IsSeparated f]
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) :
    let _ : ∀ i, Algebra R Γ(X, (U i).1) := fun i ↦ chartAlgebra f (U i)
    let _ : ∀ j, Algebra R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ chartAlgebra f (atlasPrincipalOpen U j)
    let _ : ∀ i, Algebra.FiniteType R Γ(X, (U i).1) :=
      fun i ↦ atlasChartAlgebra_finiteType f (U i)
    let _ : ∀ j, Algebra.FiniteType R Γ(X, (atlasPrincipalOpen U j).1) :=
      fun j ↦ atlasChartAlgebra_finiteType f (atlasPrincipalOpen U j)
    ∀ x : OccurrenceStage, ∃ y : OccurrenceStage, x ≤ y ∧
      ∀ i j : Shrink.{u} ι, IsAffineOpen (V y i ⊓ V y j) := by
  intro _ _ _ _ x
  let _ : X.IsSeparated := ⟨by
    simpa only [terminal.comp_from] using
      (inferInstance : IsSeparated (f ≫ terminal.from (Spec R)))⟩
  let _ := finitePrincipalAtlas_gluingStage_filtered U f
  let F := finitePrincipalAtlasGluedDiagram U f
  let c := finitePrincipalAtlasCone U f hU
  let VV (s : OccurrenceStageᵒᵖ) (i : Shrink.{u} ι) : (F.obj s).Opens := V s.unop i
  let _ : c.pt.IsSeparated := inferInstanceAs X.IsSeparated
  let _ (s : OccurrenceStageᵒᵖ) : QuasiSeparatedSpace (F.obj s) :=
    principalOccurrenceStageGlueData_quasiSeparatedSpace (dst := D) (a := AA) (b := BB) E s.unop
  let _ {s t : OccurrenceStageᵒᵖ} (g : s ⟶ t) : IsAffineHom (F.map g) :=
    principalOccurrenceGluedDiagram_map_isAffineHom (dst := D) (a := AA) (b := BB) E g
  have hV (s : OccurrenceStageᵒᵖ) (i : Shrink.{u} ι) : IsAffineOpen (VV s i) :=
    principalOccurrenceGluedChartOpen_isAffine (dst := D) (a := AA) (b := BB) E s.unop i
  have hcart {s t : OccurrenceStageᵒᵖ} (g : s ⟶ t) (i : Shrink.{u} ι) :
      F.map g ⁻¹ᵁ VV t i = VV s i :=
    principalOccurrenceGluedChartOpen_preimage
      (dst := D) (a := AA) (b := BB) E t.unop s.unop (leOfHom g.unop) i
  have hlim (i : Shrink.{u} ι) : IsAffineOpen (c.π.app (.op x) ⁻¹ᵁ VV (.op x) i) := by
    have he : c.π.app (.op x) ⁻¹ᵁ VV (.op x) i =
        (U ((equivShrink.{u} ι).symm i)).1 :=
      TopologicalSpace.Opens.ext ((finitePrincipalAtlasProjection_preimage U f hU x i).trans
        (congrArg SetLike.coe (U ((equivShrink.{u} ι).symm i)).2.opensRange_fromSpec))
    exact he.symm ▸ (U ((equivShrink.{u} ι).symm i)).2
  obtain ⟨y, g, hy⟩ := exists_cartesianAtlas_affine_intersections F c
    (finitePrincipalAtlasIsLimit U f hU) VV hV hcart (.op x) hlim
  exact ⟨y.unop, leOfHom g.unop, hy⟩

end FLT.Mazur.Approximation

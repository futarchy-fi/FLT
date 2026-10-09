/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FinitePrincipalAtlasProper
public import FLT.Mazur.FinitePrincipalAtlasLineSheaf
public import FLT.Mazur.ProperStageAmpleFiberDescent

/-!
# A proper occurrence line with the specified ample fiber

The chosen original line extends to a proper occurrence stage. Its ample
residue fiber descends further through the proper fiber limit; composition
retains the isomorphism recovering that same original line.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

/-- The specified line extends to a proper occurrence stage with its chosen fiber ample. -/
theorem exists_finitePrincipalAtlas_lineSheaf_ample_fiber
    (hU : TopologicalSpace.IsOpenCover (fun i ↦ (U i).1)) (L : X.Modules)
    (e : ∀ i, Nonempty (L.restrict (U i).1.ι ≅ structureModule (U i).1.toScheme))
    (s : Spec R) (hA : AmpleLineBundle ((Scheme.Modules.pullback (f.fiberι s)).obj L)) :
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
          ((Scheme.Modules.pullback (finitePrincipalAtlasProjection U f hU y)).obj M ≅ L) ∧
          AmpleLineBundle ((Scheme.Modules.pullback
            ((principalOccurrenceGluedStructure (dst := D) (a := AA) (b := BB) E y).fiberι s)).obj
              M) := by
  intro _ _ _ _ x
  obtain ⟨y, hxy, hy, M, hM, ⟨rec⟩⟩ := exists_finitePrincipalAtlas_lineSheaf U f hU L e x
  let _ := finitePrincipalAtlas_gluingStage_filtered U f
  let F := finitePrincipalAtlasGluedDiagram U f
  let c := finitePrincipalAtlasCone U f hU
  let t : F ⟶ (Functor.const OccurrenceStageᵒᵖ).obj (Spec R) :=
    principalOccurrenceGluedToBase (dst := D) (a := AA) (b := BB) E
  let _ : IsProper (t.app (.op y)) := hy
  let _ {j k : OccurrenceStageᵒᵖ} (a : j ⟶ k) : IsClosedImmersion (F.map a) :=
    principalOccurrenceGluedDiagram_map_isClosedImmersion (dst := D) (a := AA) (b := BB) E a
  have hAM : AmpleLineBundle
      ((Scheme.Modules.pullback (f.fiberι s)).obj
        ((Scheme.Modules.pullback (c.π.app (.op y))).obj M)) :=
    hA.of_iso ((Scheme.Modules.pullback (f.fiberι s)).mapIso rec)
  obtain ⟨r, hr⟩ := exists_properStage_ample_fiber («D» := F) t (.op y) c
    (finitePrincipalAtlasIsLimit U f hU) f
    (fun j ↦ finitePrincipalAtlasProjection_over U f hU j.unop) s M hM hAM
  let N := (Scheme.Modules.pullback (F.map r.hom)).obj M
  have he : F.map r.hom ≫ t.app (.op y) = t.app r.left :=
    (t.naturality r.hom).trans (Category.comp_id _)
  have hproper : IsProper (t.app r.left) := he ▸
    (inferInstance : IsProper (F.map r.hom ≫ t.app (.op y)))
  refine ⟨r.left.unop, hxy.trans (leOfHom r.hom.unop), hproper, N,
    hM.pullback (F.map r.hom), ⟨?_⟩, hr⟩
  exact (Scheme.Modules.pullbackComp (c.π.app r.left) (F.map r.hom)).app M ≪≫
    (Scheme.Modules.pullbackCongr (c.w r.hom)).app M ≪≫ rec

end FLT.Mazur.Approximation

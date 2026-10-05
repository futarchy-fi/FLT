/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedProjPullbackEvaluation
public import FLT.Mazur.SectionGradedProjConstruction
public import FLT.Mazur.AmpleAffinePullback

/-!
# Naturality of the canonical section-ring Proj map

Positive-power generation persists under arbitrary pullback. Whenever the
section-ring pullback induces a global Proj map, the canonical maps commute.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousIdeal
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjNaturality
open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionGradedProjConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme} (p : Y ⟶ X) (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]

/-- Positive-power generation persists under every scheme pullback. -/
lemma positivePowerGenerated_pullback (h : PositivePowerGenerated L) :
    PositivePowerGenerated ((pullback p).obj L) := by
  intro y
  obtain ⟨n, hn, s, hs⟩ := h (p y)
  refine ⟨n, hn, (tensorPowerIso p L n).hom.app ⊤ (pullGlobal p _ s), ?_⟩
  rw [sectionGeneratorOpen_iso, sectionGeneratorOpen_pullGlobal (hL.out.tensorPower n)]
  exact hs

/-- Pullback preserves the line-bundle condition. -/
local instance pulledLine : Fact (LocallyFreeRankOne ((pullback p).obj L)) :=
  ⟨hL.out.pullback p⟩

/-- The canonical maps commute with the Proj map induced by actual section pullback. -/
@[reassoc]
lemma toProj_map (h : PositivePowerGenerated L)
    (hφ : (grade ((pullback p).obj L) ⊤)₊ ≤
      (grade L ⊤)₊.map (SectionGradedPullback.gradedRingHom p L)) :
    toProj ((pullback p).obj L) (positivePowerGenerated_pullback p L h) ≫
      Proj.map (SectionGradedPullback.gradedRingHom p L) hφ = p ≫ toProj L h := by
  obtain ⟨𝒰, e, d, s, hd, hs⟩ := exists_generating_cover L h
  apply Scheme.Cover.hom_ext (𝒰.pullback₁ p)
  intro i
  let k := CategoryTheory.Limits.pullback.fst p (𝒰.f i)
  let l := CategoryTheory.Limits.pullback.snd p (𝒰.f i)
  have hc : k ≫ p = l ≫ 𝒰.f i := CategoryTheory.Limits.pullback.condition
  let e' : (pullback (k ≫ p)).obj L ≅ structureModule _ := by
    rw [hc]
    exact SectionGradedProjChart.pullTrivialization (𝒰.f i) L (e i) l
  let e'' := (pullbackComp k p).app L ≪≫ e'
  have hi : IsIso (globalSectionHom _ (pullGlobal (k ≫ p) (tensorPower L (d i)) (s i))) := by
    rw [hc]
    exact SectionGradedProjChart.pullGenerator_isIso_of_ringHom _ L _ (s i)
      (SectionGradedProjChart.ringHom_isUnit_pullback (𝒰.f i) L (e i) l
        (SectionGradedProjChart.pullTrivialization (𝒰.f i) L (e i) l) (s i) (hs i))
  have hu := SectionGradedProjChart.ringHom_isUnit_of_pullGenerator (k ≫ p) L e' (s i)
  have hv := SectionGradedProjPullbackEvaluation.ringHom_isUnit_pull_section
    p k L e'' e' (s i) hu
  change k ≫ (toProj _ _ ≫ _) = k ≫ (p ≫ toProj L h)
  rw [← Category.assoc, toProj_comp _ _ k e'' _ (hd i) hv,
    ← Category.assoc, toProj_comp L h (k ≫ p) e' (s i) (hd i) hu]
  have hm : SectionGradedPullback.ringHom p L (of L ⊤ (d i) (s i)) =
      of ((pullback p).obj L) ⊤ (d i) (SectionGradedPullback.pull p L (d i) ⊤ (s i)) :=
    SectionGradedPullback.sumMap_of p L (d i) (s i)
  have hv' : IsUnit (SectionGradedProjChart.ringHom k ((pullback p).obj L) e''
      (SectionGradedPullback.ringHom p L (of L ⊤ (d i) (s i)))) := by
    rw [hm]
    exact hv
  simpa only [hm] using
    SectionGradedProjPullbackEvaluation.toProj_map p k L e'' e' hφ (s i) (hd i) hv' hu


end FLT.Mazur.SectionGradedProjNaturality

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjUnitChartOpens
public import FLT.Mazur.SectionGradedProjConstruction
public import FLT.Mazur.AmpleAffinePullback

/-!
# Exact generator opens of the canonical section-ring Proj morphism

Every positive homogeneous section pulls back to its actual generator open.
The equality is proved locally in arbitrary line coordinates, then glued.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjOpens
open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionGradedCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme} (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]

/-- The coordinate basic open is the inverse image of the actual generator open. -/
lemma coordinate_basicOpen (p : Y ⟶ X) (e : (pullback p).obj L ≅ structureModule Y)
    (n : ℕ) (s : Γ(tensorPower L n, ⊤)) :
    Y.basicOpen (SectionGradedProjChart.ringHom p L e (of L ⊤ n s)) =
      p ⁻¹ᵁ sectionGeneratorOpen (tensorPower L n) s := by
  rw [SectionGradedProjChart.ringHom_of]
  change Y.basicOpen ((tensorPowerTrivialization e n).hom.app ⊤
    ((tensorPowerIso p L n).hom.app ⊤ (pullGlobal p (tensorPower L n) s))) = _
  rw [← sectionGeneratorOpen_structure, sectionGeneratorOpen_iso,
    sectionGeneratorOpen_iso, sectionGeneratorOpen_pullGlobal (hL.out.tensorPower n)]

/-- A local section-ring chart has exact inverse images of all positive basic opens. -/
lemma chart_preimage_basicOpen (p : Y ⟶ X)
    (e : (pullback p).obj L ≅ structureModule Y)
    {d n : ℕ} (s : Γ(tensorPower L d, ⊤)) (t : Γ(tensorPower L n, ⊤))
    (hd : 0 < d) (hn : 0 < n)
    (hs : IsUnit (SectionGradedProjChart.ringHom p L e (of L ⊤ d s))) :
    SectionGradedProjChart.toProj p L e (of L ⊤ d s) hs ⟨s, rfl⟩ hd ⁻¹ᵁ
      Proj.basicOpen (grade L ⊤) (of L ⊤ n t) =
        p ⁻¹ᵁ sectionGeneratorOpen (tensorPower L n) t := by
  rw [SectionGradedProjChart.toProj,
    GradedProjUnitChartOpens.toProj_preimage_basicOpen (grade L ⊤)
      (SectionGradedProjChart.ringHom p L e)
      (f := of L ⊤ d s) (g := of L ⊤ n t)
      (show of L ⊤ d s ∈ grade L ⊤ d from ⟨s, rfl⟩) hd
      (show of L ⊤ n t ∈ grade L ⊤ n from ⟨t, rfl⟩) hn hs]
  exact coordinate_basicOpen L p e n t

/-- Every positive homogeneous basic open pulls back to its actual generator open. -/
lemma toProj_preimage_basicOpen (h : SectionGradedProjConstruction.PositivePowerGenerated L)
    {n : ℕ} (t : Γ(tensorPower L n, ⊤)) (hn : 0 < n) :
    SectionGradedProjConstruction.toProj L h ⁻¹ᵁ Proj.basicOpen (grade L ⊤) (of L ⊤ n t) =
      sectionGeneratorOpen (tensorPower L n) t := by
  obtain ⟨𝒰, e, d, s, hd, hs⟩ := SectionGradedProjConstruction.exists_generating_cover L h
  ext x
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  have he : 𝒰.f i ⁻¹ᵁ (SectionGradedProjConstruction.toProj L h ⁻¹ᵁ
      Proj.basicOpen (grade L ⊤) (of L ⊤ n t)) =
        𝒰.f i ⁻¹ᵁ sectionGeneratorOpen (tensorPower L n) t := by
    rw [← Scheme.Hom.comp_preimage,
      SectionGradedProjConstruction.toProj_comp L h (𝒰.f i) (e i) (s i) (hd i) (hs i)]
    exact chart_preimage_basicOpen L (𝒰.f i) (e i) (s i) t (hd i) hn (hs i)
  exact congrArg (fun U ↦ y ∈ U) he |>.to_iff

end FLT.Mazur.SectionGradedProjOpens

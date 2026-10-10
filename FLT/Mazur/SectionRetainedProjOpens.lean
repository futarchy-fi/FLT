/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedProjConstruction
public import FLT.Mazur.SectionGradedProjOpens

/-!
# Exact generator opens of the retained Proj morphism

Every positive retained section has its original generator open as the
inverse image of its Proj basic open. This is proved on the original
trivializing cover and does not identify the source with a replacement scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.SectionRetainedProjOpens

open FCurve ModuleLineBundleTensorPullback SectionGradedSum
open SectionRetainedChartComparison SectionRetainedProjConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme} (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]

/-- A local retained chart pulls every positive basic open back to its original generator open. -/
theorem chart_preimage_basicOpen (p : Y ⟶ X)
    (e : (pullback p).obj L ≅ structureModule Y)
    {d n : ℕ} (s : Γ(tensorPower L (q * d), ⊤)) (t : Γ(tensorPower L (q * n), ⊤))
    (hd : 0 < d) (hn : 0 < n)
    (hs : IsUnit (SectionGradedProjChart.ringHom p L e (of L ⊤ (q * d) s))) :
    SectionRetainedProjChart.toProj p L e q (insertion L q d s) hs
      (insertion_mem L q d s) hd ⁻¹ᵁ
        Proj.basicOpen (RetainedSubringGrading.grade (grade L ⊤) q) (insertion L q n t) =
      p ⁻¹ᵁ sectionGeneratorOpen (tensorPower L (q * n)) t := by
  rw [SectionRetainedProjChart.toProj,
    GradedProjUnitChartOpens.toProj_preimage_basicOpen _
      (SectionRetainedProjChart.ringHom p L e q)
      (insertion_mem L q d s) hd (insertion_mem L q n t) hn hs]
  exact SectionGradedProjOpens.coordinate_basicOpen L p e (q * n) t

/-- The constructed retained Proj map has the exact original section-generator inverse images. -/
theorem toProj_preimage_basicOpen (h : PositivePowerGenerated L q)
    {n : ℕ} (t : Γ(tensorPower L (q * n), ⊤)) (hn : 0 < n) :
    toProj L q h ⁻¹ᵁ
      Proj.basicOpen (RetainedSubringGrading.grade (grade L ⊤) q) (insertion L q n t) =
        sectionGeneratorOpen (tensorPower L (q * n)) t := by
  obtain ⟨𝒰, e, d, s, hd, hs⟩ := exists_generating_cover L q h
  ext x
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  have he : 𝒰.f i ⁻¹ᵁ (toProj L q h ⁻¹ᵁ
      Proj.basicOpen (RetainedSubringGrading.grade (grade L ⊤) q) (insertion L q n t)) =
        𝒰.f i ⁻¹ᵁ sectionGeneratorOpen (tensorPower L (q * n)) t := by
    rw [← Scheme.Hom.comp_preimage, toProj_comp L q h (𝒰.f i) (e i) (s i) (hd i) (hs i)]
    exact chart_preimage_basicOpen L q (𝒰.f i) (e i) (s i) t (hd i) hn (hs i)
  exact congrArg (fun U ↦ y ∈ U) he |>.to_iff

end FLT.Mazur.SectionRetainedProjOpens

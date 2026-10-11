/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedCoefficientOpens
public import FLT.Mazur.PolygonPositiveRetainedStage
public import FLT.Mazur.PolygonVeroneseCoefficientMap

/-!
# Coefficient-image charts on every original stage

The coefficient-image basic opens pull back along the original stage maps to
exactly the coefficient pullbacks of the original basic opens. They cover stages.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleEval boundaryLine family
  SectionRetainedProjConstruction.toProj
variable {K L : Type} [Field K] [Field L] (f : K →+* L) (n : ℕ) (h : 2 ≤ n)
  [NeZero n] (q : ℕ) [NeZero q]
  (hK : exactVeroneseStep K n h ∣ q) (hL : exactVeroneseStep L n h ∣ q)

/-- The actual coefficient image has the expected basic-open preimage on every original stage. -/
theorem originalStageToMultipleProj_coefficient_basicOpen (m : ℕ) {d : ℕ}
    (s : CompatibleVeroneseSections K n h q) (hs : s ∈ compatibleVeroneseGrade K n h q d)
    (hd : 0 < d) :
    originalStageToMultipleProj L n h q hL m ⁻¹ᵁ
        Proj.basicOpen (compatibleVeroneseGrade L n h q)
          (compatibleVeroneseCoefficientMap f n h q s) =
      stageCoefficientFamily f m n h ⁻¹ᵁ (originalStageToMultipleProj K n h q hK m ⁻¹ᵁ
        Proj.basicOpen (compatibleVeroneseGrade K n h q) s) := by
  let _ : GradedRing (RetainedSubringGrading.grade
      (SectionGradedSum.grade (boundaryLine K m n h) ⊤) q) :=
    boundaryVeroneseGradedRing K n h q (NeZero.pos q) m
  let _ : GradedRing (RetainedSubringGrading.grade
      (SectionGradedSum.grade (boundaryLine L m n h) ⊤) q) :=
    boundaryVeroneseGradedRing L n h q (NeZero.pos q) m
  have he : boundaryVeroneseEvaluation L n h q m (compatibleVeroneseCoefficientMap f n h q s) =
      SectionRetainedLineEvaluation.map (stageCoefficientFamily f m n h)
        (boundaryLine K m n h) (boundaryLine L m n h) (coefficientBoundaryLineIso f m n h) q
        (boundaryVeroneseEvaluation K n h q m s) :=
    Subtype.ext (compatibleVeroneseCoefficientMap_eval f n h q m s)
  simp only [originalStageToMultipleProj, Scheme.Hom.comp_preimage,
    multipleVeroneseProjToCompatible_basicOpen, boundaryPositiveRetainedIso_hom]
  rw [he]
  exact SectionRetainedCoefficientOpens.toProj_preimage_image _ _ _ _ q _ _ _
    ((boundaryVeroneseEvaluation K n h q m).map_mem hs) hd

include hK

/-- Coefficient-image charts already cover every actual finite stage. -/
theorem coefficientImage_stage_cover (m : ℕ) :
    (⨆ i : Σ d : PNat, compatibleVeroneseGrade K n h q d,
      originalStageToMultipleProj L n h q hL m ⁻¹ᵁ
        Proj.basicOpen (compatibleVeroneseGrade L n h q)
          (compatibleVeroneseCoefficientMap f n h q i.2)) = ⊤ := by
  apply top_unique
  intro x _
  let y := originalStageToMultipleProj K n h q hK m (stageCoefficientFamily f m n h x)
  obtain ⟨i, z, hz⟩ :=
    (Proj.affineOpenCover (compatibleVeroneseGrade K n h q)).openCover.exists_eq y
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨i, ?_⟩
  rw [originalStageToMultipleProj_coefficient_basicOpen f n h q hK hL m i.2 i.2.property
    i.1.property]
  change y ∈ Proj.basicOpen (compatibleVeroneseGrade K n h q) i.2
  rw [← hz, ← Proj.opensRange_awayι _ _ i.2.property i.1.property]
  exact ⟨z, rfl⟩

end FLT.Mazur.PolygonInfinitesimalStages

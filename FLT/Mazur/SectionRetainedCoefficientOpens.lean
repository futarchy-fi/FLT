/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedProjOpens
public import FLT.Mazur.SectionRetainedLineEvaluation

/-!
# Retained basic opens under the original line pullback

The inverse images of coefficient-image basic opens agree on the actual schemes,
without first assuming the coefficient map is globally defined on Proj.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.SectionRetainedCoefficientOpens
open FCurve ModuleLineBundleTensorPullback SectionGradedSum
open SectionRetainedChartComparison SectionRetainedProjConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] tensorPower ModuleSheafTensor.tensor
variable {X Y : Scheme} (p : Y ⟶ X) (L : X.Modules) (M : Y.Modules)
  [hL : Fact (LocallyFreeRankOne L)] [Fact (LocallyFreeRankOne M)]
  (e : (pullback p).obj L ≅ M)

omit [Fact (LocallyFreeRankOne M)] in
/-- The original section pullback has precisely the inverse-image generator open. -/
theorem sectionMap_generatorOpen (d : ℕ) (s : Γ(tensorPower L d, ⊤)) :
    sectionGeneratorOpen (tensorPower M d) (SectionGradedLinePullback.sectionMap p e d ⊤ s) =
      p ⁻¹ᵁ sectionGeneratorOpen (tensorPower L d) s := by
  change sectionGeneratorOpen (tensorPower M d)
    ((tensorPowerCongr e d).hom.app ⊤
      ((tensorPowerIso p L d).hom.app ⊤ (pullGlobal p (tensorPower L d) s))) = _
  rw [sectionGeneratorOpen_iso, sectionGeneratorOpen_iso,
    sectionGeneratorOpen_pullGlobal (hL.out.tensorPower d)]

variable (q : ℕ)
  [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]
  [GradedRing (RetainedSubringGrading.grade (grade M ⊤) q)]

/-- Coefficient-image basic opens pull back correctly before any global Proj map is constructed. -/
theorem toProj_preimage_image (hX : PositivePowerGenerated L q) (hY : PositivePowerGenerated M q)
    (f : RetainedSubringGrading.ring (grade L ⊤) q) {d : ℕ}
    (hf : f ∈ RetainedSubringGrading.grade (grade L ⊤) q d) (hd : 0 < d) :
    toProj M q hY ⁻¹ᵁ Proj.basicOpen (RetainedSubringGrading.grade (grade M ⊤) q)
        (SectionRetainedLineEvaluation.map p L M e q f) =
      p ⁻¹ᵁ (toProj L q hX ⁻¹ᵁ
        Proj.basicOpen (RetainedSubringGrading.grade (grade L ⊤) q) f) := by
  obtain ⟨s, hs⟩ := hf
  have he : insertion L q d s = f := Subtype.ext hs
  subst f
  rw [SectionRetainedLineEvaluation.map_insertion,
    SectionRetainedProjOpens.toProj_preimage_basicOpen _ _ hY _ hd,
    SectionRetainedProjOpens.toProj_preimage_basicOpen _ _ hX _ hd]
  exact sectionMap_generatorOpen p L M e (q * d) s

end FLT.Mazur.SectionRetainedCoefficientOpens

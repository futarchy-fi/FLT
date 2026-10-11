/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedProjConstruction

/-!
# Canonical retained maps on arbitrary homogeneous coordinates

The canonical map agrees with evaluation on every positive homogeneous
retained element whose coordinate is a unit, without choosing an insertion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.SectionRetainedHomogeneousChart
open FCurve ModuleLineBundleTensorPullback SectionGradedSum
open SectionRetainedChartComparison SectionRetainedProjConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme} (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]

/-- Any homogeneous retained unit computes the original canonical morphism. -/
@[reassoc]
theorem toProj_comp (h : PositivePowerGenerated L q) (p : Y ⟶ X)
    (e : (pullback p).obj L ≅ structureModule Y)
    (f : RetainedSubringGrading.ring (grade L ⊤) q) {d : ℕ}
    (hf : f ∈ RetainedSubringGrading.grade (grade L ⊤) q d) (hd : 0 < d)
    (hu : IsUnit (SectionRetainedProjChart.ringHom p L e q f)) :
    p ≫ toProj L q h = SectionRetainedProjChart.toProj p L e q f hu hf hd := by
  obtain ⟨s, hs⟩ := hf
  have he : insertion L q d s = f := Subtype.ext hs
  subst f
  exact SectionRetainedProjConstruction.toProj_comp L q h p e s hd hu

end FLT.Mazur.SectionRetainedHomogeneousChart

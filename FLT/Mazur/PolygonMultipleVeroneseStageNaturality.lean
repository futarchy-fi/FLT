/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMultipleStageGeneratingCover
public import FLT.Mazur.PolygonMultipleStageUnitChart
public import FLT.Mazur.PolygonMultipleVeroneseUnitEvaluation

/-!
# Common-step comparison preserves the original finite stages

The actual stage morphisms commute with the global common-step isomorphism.
The proof uses lifted ample generators of the original stage at the larger step.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleEval boundaryLine family originalStageToMultipleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (q r : ℕ) [NeZero q] [NeZero r] (hq : exactVeroneseStep K n h ∣ q)

/-- The global common-step isomorphism preserves every original finite-stage morphism. -/
@[reassoc]
theorem originalStageToMultipleProj_comparison (m : ℕ) :
    originalStageToMultipleProj K n h q hq m ≫
      (multipleVeroneseProjIso K n h q r (NeZero.pos r)).hom =
        originalStageToMultipleProj K n h (q * r) (hq.trans (dvd_mul_right q r)) m := by
  obtain ⟨𝒰, e, d, s, hs, hd, hu⟩ := exists_multipleStageGeneratingCover K n h (q * r)
    (hq.trans (dvd_mul_right q r)) m
  apply 𝒰.hom_ext
  intro i
  have hv : IsUnit (SectionGradedProjChart.ringHom (𝒰.f i) (boundaryLine K m n h) (e i)
      (compatibleVeroneseEval K n h q m (multipleVeroneseInclusion K n h q r (s i)))) := by
    rw [multipleVeroneseInclusion_eval]
    exact hu i
  rw [← Category.assoc,
    originalStageToMultipleProj_unit K n h q hq m (𝒰.f i) (e i)
      (multipleVeroneseInclusion K n h q r (s i))
      (multipleVeroneseInclusion_mem K n h q r (d i) (s i) (hs i))
      (Nat.mul_pos (NeZero.pos r) (hd i)) hv,
    originalStageToMultipleProj_unit K n h (q * r) (hq.trans (dvd_mul_right q r)) m
      (𝒰.f i) (e i) (s i) (hs i) (hd i) (hu i)]
  exact multipleVeroneseProjIso_stageUnit K n h q r (NeZero.pos r) m
    (SectionGradedProjChart.ringHom (𝒰.f i) (boundaryLine K m n h) (e i))
    (s i) (hs i) (hd i) (hu i)

/-- The inverse common-step comparison likewise retains each original stage. -/
@[reassoc]
theorem originalStageToMultipleProj_comparison_inv (m : ℕ) :
    originalStageToMultipleProj K n h (q * r) (hq.trans (dvd_mul_right q r)) m ≫
      (multipleVeroneseProjIso K n h q r (NeZero.pos r)).inv =
        originalStageToMultipleProj K n h q hq m := by
  rw [← originalStageToMultipleProj_comparison K n h q r hq m]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.PolygonInfinitesimalStages

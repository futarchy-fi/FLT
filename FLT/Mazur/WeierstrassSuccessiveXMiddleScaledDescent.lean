/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleNodePushout
public import FLT.Mazur.ProjectiveLineScaling

/-!
# Arbitrary-target descent on the original node with scaled branch coordinates

Both coordinate scalings are retained in the restriction equations. Descent
is constructed from the full scheme pushout, with no affineness restriction
on the target.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
universe u
variable {K : Type u} [Field K] (c : K) (hc : c = 0)

/-- Cancelling an affine unit scaling is valid for whole scheme morphisms. -/
theorem middleNode_cancel_chartScaling (a : Kˣ) {Y : Scheme.{u}}
    (f g : ProjectiveLine.chart K ⟶ Y)
    (h : ProjectiveLine.chartScaling K a ≫ f = ProjectiveLine.chartScaling K a ≫ g) :
    f = g := by
  have H := congrArg (fun q => ProjectiveLine.chartScaling K a⁻¹ ≫ q) h
  simpa only [← Category.assoc, ← ProjectiveLine.chartScaling_mul, inv_mul_cancel,
    ProjectiveLine.chartScaling_one, Category.id_comp] using H

/-- The actual negative conic parameter is scaling by the unit negative one. -/
theorem middleNode_negativeParameter_eq_scaling :
    Spec.map (CommRingCat.ofHom (aeval (-X : K[X])).toRingHom) =
      ProjectiveLine.chartScaling K (-1) := by
  apply congrArg (fun q : K[X] →+* K[X] => Spec.map (CommRingCat.ofHom q))
  ext <;> simp [PolygonChartScaling.affine_X]

/-- Any compatible scaled affine branch maps descend uniquely on the original node. -/
theorem middleNode_exists_unique_scaled_desc (a b : Kˣ) {Y : Scheme.{u}}
    (f g : ProjectiveLine.chart K ⟶ Y)
    (w : ProjectiveLine.chartZero K ≫ f = ProjectiveLine.chartZero K ≫ g) :
    ∃! d : Spec (.of (MiddleNodeOpen c)) ⟶ Y,
      ProjectiveLine.chartScaling K a ≫ middleNodeFirstBranch c hc ≫ d = f ∧
      ProjectiveLine.chartScaling K b ≫ middleNodeSecondBranch c hc ≫ d = g := by
  let H := middleNodeBranches_isPushout c hc
  let f' := ProjectiveLine.chartScaling K a⁻¹ ≫ f
  let g' := ProjectiveLine.chartScaling K b⁻¹ ≫ g
  have w' : ProjectiveLine.chartZero K ≫ f' = ProjectiveLine.chartZero K ≫ g' := by
    simpa only [f', g', ProjectiveLine.chartZero_chartScaling_assoc] using w
  let d := H.desc f' g' w'
  have hf : middleNodeFirstBranch c hc ≫ d = f' := H.inl_desc f' g' w'
  have hg : middleNodeSecondBranch c hc ≫ d = g' := H.inr_desc f' g' w'
  have ha : ProjectiveLine.chartScaling K a ≫ middleNodeFirstBranch c hc ≫ d = f := by
    rw [hf]
    simp only [f', ← Category.assoc, ← ProjectiveLine.chartScaling_mul,
      mul_inv_cancel, ProjectiveLine.chartScaling_one, Category.id_comp]
  have hb : ProjectiveLine.chartScaling K b ≫ middleNodeSecondBranch c hc ≫ d = g := by
    rw [hg]
    simp only [g', ← Category.assoc, ← ProjectiveLine.chartScaling_mul,
      mul_inv_cancel, ProjectiveLine.chartScaling_one, Category.id_comp]
  refine ⟨d, ⟨ha, hb⟩, ?_⟩
  intro e he
  apply H.hom_ext
  · exact middleNode_cancel_chartScaling a _ _ (he.1.trans ha.symm)
  · exact middleNode_cancel_chartScaling b _ _ (he.2.trans hb.symm)

end FLT.Mazur.WeierstrassSuccessiveX

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineNodeNormalizationExact
public import FLT.Mazur.CyclicNodeChart
public import FLT.Mazur.ModuleExactOpenCover
public import FLT.Mazur.PolygonNormalizationComplex

/-!
# The cyclic polygon normalization short exact sequence

The product-ring normalization chart and the specified node chart commute with
both branch evaluations. Their affine short exact sequences descend over the
cyclic open cover, proving exactness of the existing sheaf maps for n ≥ 2.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.CyclicNormalizationChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonCyclicNormalizationPullback PolygonCyclicNormalizationFinite
variable (K : Type u) [Field K] (n : ℕ) (hn : 2 ≤ n)

theorem coproduct_normalization : coprodSpec K[X] K[X] ≫
    Spec.map (NodeNormalizationExact.inclusion K) = affineNormalization K := by
  apply coprod.hom_ext
  · rw [coprodSpec_inl_assoc]
    simp only [affineNormalization, coprod.inl_desc, ← Spec.map_comp]
    rfl
  · rw [coprodSpec_inr_assoc]
    simp only [affineNormalization, coprod.inr_desc, ← Spec.map_comp]
    rfl

/-- The two affine normalization branches in product-ring coordinates. -/
def lift (j : Fin n) : Spec (.of (K[X] × K[X])) ⟶ (PolygonPinching.components K n).left :=
  (asIso (coprodSpec K[X] K[X])).inv ≫ chartLift K n hn j ≫ comparison K n
instance lift_open (j : Fin n) : IsOpenImmersion (lift K n hn j) := by
  unfold lift
  infer_instance

theorem isPullback (j : Fin n) :
    IsPullback (Spec.map (NodeNormalizationExact.inclusion K)) (lift K n hn j)
      (PolygonCyclicAtlas.chart K n hn j) (PolygonCyclicAtlas.normalization K n hn).left := by
  apply (PolygonCyclicNormalizationPullback.isPullback K n hn j).of_iso
    (asIso (coprodSpec K[X] K[X])) (Iso.refl _) (asIso (comparison K n)) (Iso.refl _)
  · simpa only [asIso_hom, Iso.refl_hom, Category.comp_id] using
      (coproduct_normalization K).symm
  · simp [lift]
  · simp
  · simpa only [asIso_hom, Iso.refl_hom, Category.comp_id] using
      (comparison_normalization K n hn).symm

theorem first_coproduct : Spec.map (NodeNormalizationExact.firstValue K) ≫
    (asIso (coprodSpec K[X] K[X])).inv =
      ProjectiveLine.chartZero K ≫ (coprod.inl : ProjectiveLine.chart K ⟶
        ProjectiveLine.chart K ⨿ ProjectiveLine.chart K) := by
  apply (cancel_mono (coprodSpec K[X] K[X])).mp
  simp only [Category.assoc, asIso_inv, IsIso.inv_hom_id, Category.comp_id, coprodSpec_inl]
  rw [ProjectiveLine.chartZero, ← Spec.map_comp]
  rfl

theorem second_coproduct : Spec.map (NodeNormalizationExact.secondValue K) ≫
    (asIso (coprodSpec K[X] K[X])).inv =
      ProjectiveLine.chartZero K ≫ (coprod.inr : ProjectiveLine.chart K ⟶
        ProjectiveLine.chart K ⨿ ProjectiveLine.chart K) := by
  apply (cancel_mono (coprodSpec K[X] K[X])).mp
  simp only [Category.assoc, asIso_inv, IsIso.inv_hom_id, Category.comp_id, coprodSpec_inr]
  rw [ProjectiveLine.chartZero, ← Spec.map_comp]
  rfl

@[reassoc] theorem component_comparison (j : Fin n) :
    Sigma.ι (fun _ : Fin n ↦ ProjectiveLine.scheme K) j ≫ comparison K n =
      (PolygonPinching.componentι K n j).left :=
  ι_comp_sigmaComparison (Over.forget (Spec (.of K)))
    (fun _ : Fin n ↦ PolygonPinching.component K) j

@[reassoc] theorem first_lift (j : Fin n) :
    Spec.map (NodeNormalizationExact.firstValue K) ≫ lift K n hn j =
      (PolygonPinching.nodeι K n j).left ≫
        (PolygonBranchDifferenceSheaf.branchSection K n (by omega) false).left := by
  rw [lift, ← Category.assoc, first_coproduct]
  simp only [Category.assoc, chartLift, coprod.inl_desc_assoc, firstLift,
    component_comparison]
  rw [← Category.assoc]
  change ProjectiveLine.zero K ≫ (PolygonPinching.componentι K n j).left = _
  change _ = (PolygonPinching.nodeι K n j ≫
    PolygonBranchDifferenceSheaf.branchSection K n (by omega) false).left
  simp [PolygonBranchDifferenceSheaf.branchSection, PolygonPinching.nodeι, PolygonPinching.endpoint,
    ProjectiveLine.zeroSection]

@[reassoc] theorem second_lift (j : Fin n) :
    Spec.map (NodeNormalizationExact.secondValue K) ≫ lift K n hn j =
      (PolygonPinching.nodeι K n j).left ≫
        (PolygonBranchDifferenceSheaf.branchSection K n (by omega) true).left := by
  rw [lift, ← Category.assoc, second_coproduct]
  simp only [Category.assoc, chartLift, coprod.inr_desc_assoc, secondLift,
    component_comparison]
  rw [← Category.assoc]
  change ProjectiveLine.infinity K ≫
    (PolygonPinching.componentι K n (finRotate n j)).left = _
  change _ = (PolygonPinching.nodeι K n j ≫
    PolygonBranchDifferenceSheaf.branchSection K n (by omega) true).left
  simp [PolygonBranchDifferenceSheaf.branchSection, PolygonPinching.nodeι, PolygonPinching.endpoint,
    PolygonCyclicAtlas.next_eq_rotate, ProjectiveLine.infinitySection]
/-- The actual normalization complex of the cyclic polygon. -/
def complex : ShortComplex (PolygonCyclicAtlas.scheme K n hn).Modules :=
  PolygonNormalizationComplex.complex K n (by omega)
    (PolygonCyclicAtlas.normalization K n hn) (PolygonCyclicAtlas.nodes K n hn)
    (PolygonCyclicPushout.isPushout K n hn (by omega))

theorem chart_shortExact (j : Fin n) :
    ((complex K n hn).map (Scheme.Modules.restrictFunctor
      (PolygonCyclicAtlas.chart K n hn j))).ShortExact := by
  apply PolygonNormalizationComplex.chart_shortExact K n (by omega)
    (PolygonCyclicAtlas.normalization K n hn) (PolygonCyclicAtlas.nodes K n hn)
    (PolygonCyclicPushout.isPushout K n hn (by omega))
    (NodeNormalizationExact.inclusion K) (NodeNormalizationExact.firstValue K)
    (NodeNormalizationExact.secondValue K) (NodeNormalizationExact.nodeValue K)
    (by rw [← Spec.map_comp, NodeNormalizationExact.first_agrees])
    (by rw [← Spec.map_comp, NodeNormalizationExact.second_agrees])
    (PolygonCyclicAtlas.chart K n hn j) (lift K n hn j) (PolygonPinching.nodeι K n j).left
    (isPullback K n hn j) (CyclicNodeChart.specified_isPullback K n hn j)
    (first_lift K n hn j) (second_lift K n hn j)
  · exact Subtype.val_injective
  · intro s hs
    exact ⟨⟨s, (PolygonNodeEqualizer.mem_A s).mpr hs⟩, rfl⟩
  · intro a
    exact ⟨(Polynomial.C a, 0), by
      simp [NodeNormalizationExact.firstValue, NodeNormalizationExact.secondValue]⟩

theorem shortExact : (complex K n hn).ShortExact :=
  ModuleExactOpenCover.shortExact_of_schemeCover _ (targetCover K n hn)
    (chart_shortExact K n hn)
end FLT.Mazur.CyclicNormalizationChart

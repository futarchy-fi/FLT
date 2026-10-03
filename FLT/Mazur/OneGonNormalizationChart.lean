/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineNodeNormalizationExact
public import FLT.Mazur.PolygonNormalizationComplex

/-!
# Exactness on the pinched affine chart of the one-gon

The normalization coordinate sends zero to zero and one to infinity. The actual
coproduct maps give cartesian normalization and node squares, so their module
complex is the affine endpoint-equalizer sequence.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial
@[expose] public noncomputable section
universe u
namespace FLT.Mazur.OneGonNormalizationChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open OneGonNormalization OneGonAffineNormalization
variable (K : Type u) [Field K]
instance componentι_iso (j : Fin 1) : IsIso (PolygonPinching.componentι K 1 j).left := by
  have : IsIso (PolygonPinching.componentι K 1 j) := by
    change IsIso (Sigma.ι (fun _ : Fin 1 ↦ PolygonPinching.component K) j)
    rw [Subsingleton.elim j default, ← coproductUniqueIso_inv]
    infer_instance
  exact inferInstanceAs (IsIso ((Over.forget _).map (PolygonPinching.componentι K 1 j)))
instance nodeι_iso (j : Fin 1) : IsIso (PolygonPinching.nodeι K 1 j).left := by
  have : IsIso (PolygonPinching.nodeι K 1 j) := by
    change IsIso (Sigma.ι (fun _ : Fin 1 ↦ PolygonPinching.point K) j)
    rw [Subsingleton.elim j default, ← coproductUniqueIso_inv]
    infer_instance
  exact inferInstanceAs (IsIso ((Over.forget _).map (PolygonPinching.nodeι K 1 j)))
/-- The affine normalization chart in the specified one-component coproduct. -/
def lift : ProjectiveLine.chart K ⟶ (PolygonPinching.components K 1).left :=
  alpha K ≫ (PolygonPinching.componentι K 1 0).left
instance lift_open : IsOpenImmersion (lift K) := by unfold lift; infer_instance
theorem normalization_isPullback :
    IsPullback (Spec.map (OneGonNormalizationExact.inclusion K)) (lift K)
      (OneGonGluing.node K) (normalizationOver K).left := by
  apply (OneGonNormalizationPullback.node_isPullback K).of_iso (Iso.refl _) (Iso.refl _)
    (asIso (PolygonPinching.componentι K 1 0).left) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · simp [lift]
  · simp
  · dsimp only [Iso.refl_hom, asIso_hom]
    rw [Category.comp_id]
    exact (congrArg Over.Hom.left (componentι_normalizationOver K 0)).symm

theorem node_isPullback :
    IsPullback (Spec.map (OneGonNormalizationExact.nodeValue K))
      (PolygonPinching.nodeι K 1 0).left (OneGonGluing.node K) (nodes K).left := by
  apply IsPullback.flip
  apply IsPullback.of_horiz_isIso_mono
  exact ⟨nodeι_nodes K 0⟩
@[reassoc] theorem zero_lift : Spec.map (OneGonNormalizationExact.zeroValue K) ≫ lift K =
    (PolygonPinching.nodeι K 1 0).left ≫
      (PolygonBranchDifferenceSheaf.branchSection K 1 (by decide) false).left := by
  change ProjectiveLine.chartZero K ≫ (alpha K ≫ _) = _
  rw [← Category.assoc, zero_alpha]
  change _ = (PolygonPinching.nodeι K 1 0 ≫
    PolygonBranchDifferenceSheaf.branchSection K 1 (by decide) false).left
  simp [PolygonBranchDifferenceSheaf.branchSection, PolygonPinching.nodeι,
    PolygonPinching.endpoint, ProjectiveLine.zeroSection]
@[reassoc] theorem one_lift : Spec.map (OneGonNormalizationExact.oneValue K) ≫ lift K =
    (PolygonPinching.nodeι K 1 0).left ≫
      (PolygonBranchDifferenceSheaf.branchSection K 1 (by decide) true).left := by
  change PinchingAffineDescent.chartOne K ≫ (alpha K ≫ _) = _
  rw [← Category.assoc, one_alpha]
  change _ = (PolygonPinching.nodeι K 1 0 ≫
    PolygonBranchDifferenceSheaf.branchSection K 1 (by decide) true).left
  simp [PolygonBranchDifferenceSheaf.branchSection, PolygonPinching.nodeι,
    PolygonPinching.endpoint, ProjectiveLine.infinitySection]

/-- The actual one-gon normalization complex. -/
def complex : ShortComplex (OneGonGluing.scheme K).Modules :=
  PolygonNormalizationComplex.complex K 1 (by decide) (normalizationOver K) (nodes K)
    (OneGonGlobalPushout.isPushout K (by decide))

theorem node_shortExact :
    ((complex K).map (Scheme.Modules.restrictFunctor (OneGonGluing.node K))).ShortExact := by
  apply PolygonNormalizationComplex.chart_shortExact K 1 (by decide)
    (normalizationOver K) (nodes K) (OneGonGlobalPushout.isPushout K (by decide))
    (OneGonNormalizationExact.inclusion K) (OneGonNormalizationExact.zeroValue K)
    (OneGonNormalizationExact.oneValue K) (OneGonNormalizationExact.nodeValue K)
    (by rw [← Spec.map_comp, OneGonNormalizationExact.zero_agrees])
    (by rw [← Spec.map_comp, OneGonNormalizationExact.one_agrees])
    (OneGonGluing.node K) (lift K) (PolygonPinching.nodeι K 1 0).left
    (normalization_isPullback K) (node_isPullback K) (zero_lift K) (one_lift K)
  · exact Subtype.val_injective
  · intro p hp
    exact ⟨⟨p, (PolygonNodePresentation.mem_B p).mpr hp⟩, rfl⟩
  · intro a
    refine ⟨Polynomial.C a * (1 - Polynomial.X), ?_⟩
    simp [OneGonNormalizationExact.zeroValue, OneGonNormalizationExact.oneValue]
end FLT.Mazur.OneGonNormalizationChart

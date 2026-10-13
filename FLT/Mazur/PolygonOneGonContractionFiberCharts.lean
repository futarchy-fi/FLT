/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContractionFiber
public import FLT.Mazur.OneGonNodeNormalizationIdeal
public import FLT.Mazur.AffineSpectrumKernelIdeal
public import FLT.Mazur.AffineIdealSheafComparison

/-!
# Explicit scheme-theoretic charts of the collapsed fiber

On the retained component's original affine normalization chart the fiber
has equation X(X-1). On its full Laurent chart it is empty. Together with
the zero ideal on all omitted components, these keep the complete original
normalization charts and their scheme-theoretic fiber multiplicities.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching BaseAdicThickening
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

/-- The target node restricted to its original affine node chart retains its residue map. -/
theorem targetNode_chart_ideal :
    (targetNode K).left.ker.comap (OneGonGluing.node K) =
      (PolygonNodePresentation.bOrigin K).ker := by
  have H : IsPullback (𝟙 (Spec (.of K))) (PolygonNodePresentation.bOrigin K)
      (targetNode K).left (OneGonGluing.node K) := by
    apply IsPullback.of_horiz_isIso_mono
    constructor
    rw [Category.id_comp]
    exact OneGonNormalization.nodeι_nodes K 0
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.flip.isoPullback.hom,
    H.flip.isoPullback_hom_fst]

/-- The retained affine normalization chart has exactly the two simple endpoint equations. -/
theorem retained_node_chart_ideal :
    ((targetNode K).left.ker.comap (retainedComponent K).left).comap
        (OneGonAffineNormalization.alpha K) =
      baseIdeal (.of K[X]) (Ideal.span ({X * (X - 1)} : Set K[X])) := by
  rw [← Scheme.IdealSheafData.comap_comp]
  have he : OneGonAffineNormalization.alpha K ≫ (retainedComponent K).left =
      PinchingAffineDescent.oneBranch K ≫ OneGonGluing.node K := by
    change OneGonAffineNormalization.alpha K ≫
      (componentι K 1 0 ≫ OneGonNormalization.normalizationOver K).left = _
    rw [OneGonNormalization.componentι_normalizationOver]
    exact OneGonAffineNormalization.alpha_normalization K
  rw [he, Scheme.IdealSheafData.comap_comp, targetNode_chart_ideal]
  change (Spec.map (CommRingCat.ofHom (PolygonNodePresentation.bEval (R := K)).toRingHom)).ker.comap
    (Spec.map (CommRingCat.ofHom (PolygonNodePresentation.B (R := K)).val.toRingHom)) = _
  rw [specMap_ker_baseIdeal, baseIdeal_comap_specMap]
  exact congrArg (baseIdeal (.of K[X])) (OneGonNodeNormalizationIdeal.node_ideal_map K)

variable (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)

omit [NeZero n] in
/-- The actual contraction fiber has equation X(X-1) on the retained normalization chart. -/
theorem fiberIdeal_retained_chart :
    (fiberIdeal K n hn p q h i).comap
        (OneGonAffineNormalization.alpha K ≫ (componentι K n i ≫ p).left) =
      baseIdeal (.of K[X]) (Ideal.span ({X * (X - 1)} : Set K[X])) := by
  rw [Scheme.IdealSheafData.comap_comp, fiberIdeal_retained, retained_node_chart_ideal]

omit [NeZero n] in
/-- The same closed fiber is empty on the original retained Laurent chart. -/
theorem fiberIdeal_retained_torus :
    (fiberIdeal K n hn p q h i).comap
        (torusToComponent K ≫ componentι K n i ≫ p).left = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  change (torusToComponent K ≫ componentι K n i ≫ p).left x ∈
    ((fiberIdeal K n hn p q h i).support : Set C.left) ↔ False
  rw [fiberIdeal_support]
  exact iff_false_intro (fun hx ↦ hx ⟨x, rfl⟩)

end FLT.Mazur.PolygonOneGonContraction

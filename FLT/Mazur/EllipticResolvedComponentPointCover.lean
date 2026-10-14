/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticResolvedComponentLabels

/-!
# Every original point has a chart in the actual resolved component family

The original E₀ points use the identity torus. Primitive positive-depth points
use the retained or terminal charts with the original arithmetic parameter.
This covers unrestricted proper specializations, without asserting that every
residue-field point lifts to the generic curve.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (r : (ResidueField A)ˣ) (c₆ : A) (h6 : W.a₆ = π ^ depth * c₆)
  (hr : r ^ depth = nodeWrapParameterUnit D c₆ h6)
local notation "F" => ResidueField A

include hr in
/-- Every nonsmooth original reduction has its arithmetic parameter in an actual component chart. -/
theorem resolvedComponentChart_covers_nonsmooth
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : ¬ SmoothReduction A W P) :
    ∃ i : ResolvedComponentIndex depth,
      resolvedComponentLabel i = (nodePointLabel D P).val ∧
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := F)
        (nodeTrivializedParameter D c₆ h6 r P)).toRingHom) ≫
          resolvedComponentChart A D r i = resolvedSplitSmoothPoint A D P := by
  obtain ⟨v, hv⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq depth
    D.a₃_mem D.a₄_mem D.a₆_not_mem P hP
  have hπm : π ∈ maximalIdeal A := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have h3 : W.a₃ ∈ maximalIdeal A := Ideal.pow_le_self (by omega) D.a₃_mem
  have h4 : W.a₄ ∈ maximalIdeal A := Ideal.pow_le_self (by omega) D.a₄_mem
  have h6m : W.a₆ ∈ maximalIdeal A :=
    Ideal.pow_le_self (by have := D.depth_pos; omega) D.a₆_mem
  have hk0 : 0 < v.depth := by
    by_contra hn
    exact hP ((v.smooth_iff hπm h3 h4 h6m).mpr (by omega))
  by_cases he : v.depth = depth / 2
  · have hk : 0 < depth / 2 := by omega
    by_cases hm : 2 * (depth / 2) = depth
    · refine ⟨.terminalMiddle hk hm, ?_,
        resolvedTerminalMiddleSmoothChart_point A D r hk c₆ h6 P v he hm hr⟩
      simpa only [resolvedComponentLabel, he] using
        (nodePointLabel_val_positive D v (by omega) (Or.inl (by omega))).symm
    · have hp : 2 * (depth / 2) < depth := by omega
      by_cases hb : v.b ∈ maximalIdeal A
      · refine ⟨.terminalPositive hk hp, ?_,
          resolvedTerminalPositiveSmoothChart_point A D r hk c₆ h6 P v he hp hb⟩
        simpa only [resolvedComponentLabel, he] using
          (nodePointLabel_val_positive D v (by omega) (Or.inr hb)).symm
      · refine ⟨.terminalNegative hk hp, ?_,
          resolvedTerminalNegativeSmoothChart_point A D r hk c₆ h6 P v he hp hr
            (notMem_maximalIdeal.mp hb)⟩
        simpa only [resolvedComponentLabel, he] using
          (nodePointLabel_val_negative D v hk0 (by omega)
            (notMem_maximalIdeal.mp hb)).symm
  · have hj : v.depth < depth / 2 := by omega
    by_cases hb : v.b ∈ maximalIdeal A
    · refine ⟨.retainedPositive v.depth hk0 hj, ?_,
        resolvedRetainedPositiveSmoothChart_point A D r v.depth hk0 hj c₆ h6 P v rfl hb⟩
      exact (nodePointLabel_val_positive D v (by omega) (Or.inr hb)).symm
    · refine ⟨.retainedNegative v.depth hk0 hj, ?_,
        resolvedRetainedNegativeSmoothChart_point A D r v.depth hk0 hj c₆ h6 P v rfl hr
          (notMem_maximalIdeal.mp hb)⟩
      exact (nodePointLabel_val_negative D v hk0 (by omega)
        (notMem_maximalIdeal.mp hb)).symm

include hr in
/-- Every original generic point factors over the residue field through one actual torus chart. -/
theorem resolvedComponentChart_covers_specialization
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    ∃ (i : ResolvedComponentIndex depth) (t : Spec (.of F) ⟶ Spec (.of F[T;T⁻¹])),
      resolvedComponentLabel i = (nodePointLabel D P).val ∧
      t ≫ (MultiplicativeGroupScheme.gm F).hom = 𝟙 _ ∧
        t ≫ resolvedComponentChart A D r i = resolvedSplitSmoothPoint A D P := by
  by_cases hP : SmoothReduction A W P
  · refine ⟨.identity, resolvedIdentityPointCoordinate A D ⟨P, hP⟩, ?_,
      resolvedIdentityPointCoordinate_structure A D ⟨P, hP⟩,
      resolvedIdentityPointCoordinate_smoothChart A D ⟨P, hP⟩⟩
    simp only [resolvedComponentLabel, (nodePointLabel_eq_zero_iff D P).mpr hP, ZMod.val_zero]
  · obtain ⟨i, hl, hi⟩ := resolvedComponentChart_covers_nonsmooth A D r c₆ h6 hr P hP
    refine ⟨i, _, hl, ?_, hi⟩
    rw [← resolvedComponentChart_structure A D r i, ← Category.assoc, hi]
    exact resolvedSplitSmoothPoint_structure A D P

include hr in
/-- Every point of every unrestricted specialized morphism lies in this chart family. -/
theorem resolvedComponentChart_range_covers_specialization
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    Set.range (resolvedSplitSmoothPoint A D P) ⊆
      ⋃ i : ResolvedComponentIndex depth, Set.range (resolvedComponentChart A D r i) := by
  obtain ⟨i, t, _, _, ht⟩ := resolvedComponentChart_covers_specialization A D r c₆ h6 hr P
  rintro _ ⟨x, rfl⟩
  apply Set.mem_iUnion.mpr
  refine ⟨i, t x, ?_⟩
  exact congrArg (fun f => f x) ht

end FLT.Mazur.WeierstrassDividedDepth

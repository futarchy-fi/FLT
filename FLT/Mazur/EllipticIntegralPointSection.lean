/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNormalizedIntegralLift
public import FLT.Mazur.WeierstrassProjectivePointNaturality

/-!
# The integral section of an actual generic Weierstrass point

Primitive coordinates define a section of the original glued integral cubic.
Its chart formula is independent of all normalization choices and its generic
fiber is precisely the scheme point of the original projective point.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K : Type u} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Normalized integral lifts of the same generic point give the same scheme section. -/
theorem integralLift_chart_eq (P : (W.map (algebraMap A K)).toProjective.Point)
    (j k : Fin 3) (v w : Fin 3 → A)
    (hv : (W.map (algebraMap A A)).toProjective.Equation v) (hj : v j = 1)
    (hw : (W.map (algebraMap A A)).toProjective.Equation w) (hk : w k = 1)
    (he : (⟦fun i => (v i : K)⟧ : PointClass K) = P.point)
    (hf : (⟦fun i => (w i : K)⟧ : PointClass K) = P.point) :
    integralChartPoint W j v hv hj = integralChartPoint W k w hw hk := by
  apply (integralChartPoint_eq_iff W j k v w hv hj hw hk).mpr
  have hc := (normalized_projective_eq_iff j k (fun i => (v i : K))
    (fun i => (w i : K)) (congrArg (algebraMap A K) hj)
      (congrArg (algebraMap A K) hk)).mp (he.trans hf.symm)
  intro i
  apply IsFractionRing.injective A K
  exact hc i

/-- An actual integral section with normalized coordinates for the original point exists. -/
theorem exists_integralPointSection
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    ∃ s : Spec (.of A) ⟶ integralCurve W,
      ∃ (j : Fin 3) (v : Fin 3 → A)
        (hv : (W.map (algebraMap A A)).toProjective.Equation v) (hj : v j = 1),
        (⟦fun i => (v i : K)⟧ : PointClass K) = P.point ∧
        s = integralChartPoint W j v hv hj := by
  obtain ⟨j, v, hv, hj, he, _⟩ := exists_normalized_integral_lift A W P
  have hv' : (W.map (algebraMap A A)).toProjective.Equation v := by
    simpa only [Algebra.algebraMap_self, WeierstrassCurve.map_id] using hv
  exact ⟨integralChartPoint W j v hv' hj, j, v, hv', hj, he, rfl⟩

/-- The section of the original integral cubic attached to the original generic point. -/
def integralPointSection (P : (W.map (algebraMap A K)).toProjective.Point) :
    Spec (.of A) ⟶ integralCurve W :=
  Classical.choose (exists_integralPointSection A W P)

/-- Every normalized integral lift computes the same integral section. -/
theorem integralPointSection_chart
    (P : (W.map (algebraMap A K)).toProjective.Point) (j : Fin 3) (v : Fin 3 → A)
    (hv : (W.map (algebraMap A A)).toProjective.Equation v) (hj : v j = 1)
    (he : (⟦fun i => (v i : K)⟧ : PointClass K) = P.point) :
    integralPointSection A W P = integralChartPoint W j v hv hj := by
  obtain ⟨k, w, hw, hk, hf, hs⟩ := Classical.choose_spec (exists_integralPointSection A W P)
  exact hs.trans (integralLift_chart_eq A W P k j w v hw hk hv hj hf he)

/-- The constructed morphism is a section over the original valuation ring. -/
@[reassoc] theorem integralPointSection_structure
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    integralPointSection A W P ≫ integralCurveStructure W = 𝟙 _ := by
  obtain ⟨j, v, hv, hj, he, hs⟩ := Classical.choose_spec (exists_integralPointSection A W P)
  rw [show integralPointSection A W P = _ from hs, integralChartPoint_structure]
  exact Spec.map_id _

/-- Restricting the section to the generic fiber recovers the exact original scheme point. -/
theorem integralPointSection_generic
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ integralPointSection A W P =
      (projectiveToIntegral W P).left := by
  obtain ⟨j, v, hv, hj, he, hs⟩ := Classical.choose_spec (exists_integralPointSection A W P)
  have hv' : W.toProjective.Equation v := by
    simpa only [Algebra.algebraMap_self, WeierstrassCurve.map_id] using hv
  have hk : (fun i => (v i : K)) j = 1 := congrArg (algebraMap A K) hj
  rw [show integralPointSection A W P = _ from hs]
  exact (integralChartPoint_natural W j v hv hj (Algebra.ofId A K)
    (hv'.map (algebraMap A K)) hk).trans
      (projectiveToIntegral_chart W P j _ (hv'.map (algebraMap A K)) hk he).symm

/-- Distinct original generic points have distinct integral sections. -/
theorem integralPointSection_injective : Function.Injective (integralPointSection A W) := by
  intro P Q h
  apply projectiveToIntegral_injective W
  apply Over.OverMorphism.ext
  rw [← integralPointSection_generic A W P, ← integralPointSection_generic A W Q, h]

end FLT.Mazur.WeierstrassIntegralChart

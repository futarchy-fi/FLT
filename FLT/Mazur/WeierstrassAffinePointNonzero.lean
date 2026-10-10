/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassNonzeroPointAffine

/-!
# The original affine chart avoids the origin

A point of the actual affine chart cannot equal the infinity section.
The coordinate comparison proves this over every nontrivial coefficient algebra.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R S : Type} [CommRing R] [CommRing S] [Nontrivial S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- An affine chart evaluation never equals the actual base-changed infinity section. -/
theorem affine_evaluation_ne_zero (f : Coordinate W 2 →ₐ[R] S) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W 2 ≠
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ integralCurveZero W := by
  intro h
  have hz : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ integralCurveZero W =
      Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := S) W).toRingHom) ≫
        integralCurveChart W 1 := by
    conv_rhs => rw [chartInfinityEvaluation_base]
    rw [integralCurveZero, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hc := (chart_algHom_global_eq_iff W 2 1 f
    (chartInfinityEvaluation (S := S) W)).mp (h.trans hz) 2
  simp at hc

variable {K : Type} [Field K] [Algebra R K]

/-- Every field-valued affine chart morphism avoids the origin over its given base map. -/
theorem affine_chart_point_ne_zero (q : Spec (.of K) ⟶ chartScheme W 2)
    (hq : q ≫ chartStructure W 2 = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    q ≫ integralCurveChart W 2 ≠
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ integralCurveZero W := by
  have h := affine_evaluation_ne_zero W (fieldChartAlgHom W 2 q hq)
  rwa [fieldChartAlgHom_spec] at h

/-- Factoring through the original affine chart is equivalent to being a nonidentity point. -/
theorem field_point_affine_iff (hΔ : IsUnit W.Δ)
    (P : integralGroupFieldPoints (K := K) W hΔ) :
    (∃ q : Spec (.of K) ⟶ chartScheme W 2,
      q ≫ integralCurveChart W 2 = P.left) ↔ P ≠ 1 := by
  constructor
  · rintro ⟨q, hq⟩ hP
    have hb : q ≫ chartStructure W 2 = Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      rw [← integralCurveChart_structure, ← Category.assoc, hq]
      exact P.w
    apply affine_chart_point_ne_zero W q hb
    rw [hq, hP]
    rfl
  · exact nonzeroPoint_factor W hΔ P

end FLT.Mazur.WeierstrassIntegralChart

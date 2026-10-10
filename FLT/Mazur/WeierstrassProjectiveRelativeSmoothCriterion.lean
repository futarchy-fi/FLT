/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineRelativeSmoothCriterion

/-!
# Detecting nonsingularity in every projective chart

Smooth field-valued points in any normalized chart are classically nonsingular.
At infinity this follows directly from the equation; away from infinity one
changes to the affine chart and applies the relative tangent obstruction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassCurve.Projective

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R)

/-- Relative smoothness detects classical nonsingularity in every projective chart. -/
theorem chartFieldPoint_nonsingular_of_smooth (j : Fin 3) (f : Coordinate W j →ₐ[R] K)
    (hs : Set.range (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W j) ⊆
      integralSmoothOpen W) :
    (W.map (algebraMap R K)).toProjective.Nonsingular (f ∘ coord W j) := by
  let v := f ∘ coord W j
  have hv := chartAlgHom_equation W j f
  have hj : v j = 1 := by simp [v]
  change (W.map (algebraMap R K)).toProjective.Nonsingular v
  by_cases hz : v 2 = 0
  · have hx : v 0 = 0 := X_eq_zero_of_Z_eq_zero hv hz
    have hy : v 1 ≠ 0 := by
      intro hy
      fin_cases j <;> simp_all
    apply (nonsingular_of_Z_eq_zero hz).mpr
    refine ⟨hv, Or.inr ?_⟩
    simpa only [hx, mul_zero, zero_mul, add_zero, zero_pow two_ne_zero, sub_zero] using
      pow_ne_zero 2 hy
  · let w := (v 2)⁻¹ • v
    have hw : (W.map (algebraMap R K)).toProjective.Equation w :=
      (equation_smul v (isUnit_iff_ne_zero.mpr (inv_ne_zero hz))).mpr hv
    have hw2 : w 2 = 1 := inv_mul_cancel₀ hz
    let g := evaluation W 2 w hw hw2
    have he : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W j =
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ integralCurveChart W 2 := by
      apply (chart_algHom_global_eq_iff W j 2 f g).mpr
      intro i
      change v i = v 2 * evaluation W 2 w hw hw2 (coord W 2 i)
      rw [evaluation_coord]
      change v i = v 2 * ((v 2)⁻¹ * v i)
      rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]
    have hgs : Set.range (Spec.map (CommRingCat.ofHom g.toRingHom)) ⊆
        (chartStructure W 2).smoothLocus := by
      rw [← integralCurveChart_preimage_smooth]
      rintro _ ⟨p, rfl⟩
      have h := hs ⟨p, rfl⟩
      rw [he] at h
      exact h
    have hn := affineFieldPoint_nonsingular_of_smooth W g hgs
    apply (nonsingular_of_Z_ne_zero hz).mpr
    simpa only [g, evaluation_coord, w, Pi.smul_apply, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using hn

/-- A chart point lands in the full smooth open exactly when its coordinates are nonsingular. -/
theorem chartFieldPoint_smooth_iff (j : Fin 3) (f : Coordinate W j →ₐ[R] K) :
    Set.range (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W j) ⊆
        integralSmoothOpen W ↔
      (W.map (algebraMap R K)).toProjective.Nonsingular (f ∘ coord W j) :=
  ⟨chartFieldPoint_nonsingular_of_smooth W j f, chartFieldPoint_range_smooth W j f⟩

end FLT.Mazur.WeierstrassIntegralChart

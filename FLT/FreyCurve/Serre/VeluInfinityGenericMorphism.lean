/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityRegularMorphism

/-!
# Generic comparison of the actual infinity extension

Both the source inclusion and the target morphism retain the original affine
function-field points, comparing the actual chart presentations of the glued cubics.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] infinityTargetCoordinates infinityTargetHom

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

omit [DecidableEq K] in
/-- The two original source chart presentations give the same generic point. -/
theorem sourceInfinityChart_global :
    Spec.map (CommRingCat.ofHom (sourceInfinityChart E).toRingHom) ≫
        integralCurveChart E 1 =
      Spec.map (CommRingCat.ofHom (sourceGenericChart E).toRingHom) ≫
        integralCurveChart E 2 := by
  apply (chart_algHom_global_eq_iff E 1 2 _ _).mpr
  intro i
  fin_cases i
  · change sourceInfinityChart E (coord E 1 0) =
      sourceInfinityChart E (coord E 1 2) * sourceGenericChart E (coord E 2 0)
    simp only [sourceInfinityChart_u, sourceInfinityChart_v, sourceGenericChart_x,
      div_eq_mul_inv, mul_comm]
  · change sourceInfinityChart E (coord E 1 1) =
      sourceInfinityChart E (coord E 1 2) * sourceGenericChart E (coord E 2 1)
    rw [coord_self, map_one, sourceInfinityChart_v, sourceGenericChart_y,
      inv_mul_cancel₀ (sourceGenericY_ne_zero E)]
  · change sourceInfinityChart E (coord E 1 2) =
      sourceInfinityChart E (coord E 1 2) * sourceGenericChart E (coord E 2 2)
    rw [coord_self, map_one, mul_one]

/-- The final neighborhood inclusion retains the original source generic point. -/
@[reassoc] theorem veluInfinityOpenImmersion_generic :
    Spec.map (CommRingCat.ofHom (infinityTargetHom E G).toRingHom) ≫
        veluInfinityOpenImmersion E G =
      Spec.map (CommRingCat.ofHom (sourceGenericChart E).toRingHom) ≫
        integralCurveChart E 2 := by
  rw [← sourceInfinityChart_global E]
  simp only [veluInfinityOpenImmersion, ← Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (infinityTargetHom_algebraMap E G _).trans
    ((infinityKernelHom_algebraMap E G _).trans (infinityParameterHom_algebraMap E a))

/-- The regular infinity extension retains the original generic Vélu morphism. -/
@[reassoc] theorem veluInfinityRegularMorphism_generic
    (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q) :
    Spec.map (CommRingCat.ofHom (infinityTargetHom E G).toRingHom) ≫
        veluInfinityRegularMorphism E G hodd = veluGenericMorphism E G hodd := by
  rw [veluInfinityRegularMorphism, ← Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom
    ((infinityTargetHom E G).comp (infinityTargetChart E G hodd)).toRingHom) ≫ _ = _
  apply (chart_algHom_global_eq_iff (curve E G) 1 2 _ _).mpr
  intro i
  change infinityTargetHom E G (infinityTargetChart E G hodd (coord (curve E G) 1 i)) =
    infinityTargetHom E G (infinityTargetChart E G hodd (coord (curve E G) 1 2)) *
      veluGenericChart E G hodd (coord (curve E G) 2 i)
  simp only [infinityTargetChart, evaluation_coord, infinityTargetCoordinates_generic]
  fin_cases i
  · change _ / _ = _⁻¹ * veluGenericChart E G hodd (coord (curve E G) 2 0)
    rw [veluGenericChart_x, div_eq_mul_inv, mul_comm]
  · change 1 = _⁻¹ * veluGenericChart E G hodd (coord (curve E G) 2 1)
    rw [veluGenericChart_y, inv_mul_cancel₀ (infinityImageY_ne_zero E G)]
  · change _ = _ * veluGenericChart E G hodd (coord (curve E G) 2 2)
    rw [coord_self, map_one, mul_one]
    rfl

end WeierstrassCurve.Velu

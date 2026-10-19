/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluTranslationFieldHom
public import FLT.FreyCurve.Serre.VeluKernelTranslationInvariant

/-!
# Translation of the original source and Vélu function-field coordinates

The full field map has the actual source translation as its scheme action.
Kernel translations fix the original generic Vélu morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry RatFunc
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  {u v : K} (hQ : E.toAffine.Nonsingular u v)

/-- The uncompleted source y has exactly its original translated value. -/
theorem translationFieldHom_sourceY :
    translationFieldHom E hQ (liftY E E RatFunc.X 1) = translateY E u v := by
  rw [sourceGenericY_completed]
  simp only [map_div₀, map_sub, map_mul, map_ofNat, AlgHom.commutes,
    translationFieldHom_omega, translationFieldHom_liftX, substitution_X]
  dsimp [translationCompletedY]
  ring

omit [E.IsElliptic] in
/-- Every target lifted y uses the same original quadratic generator. -/
theorem liftY_completed (E' : WeierstrassCurve K) (f g : K⟮X⟯) :
    liftY E E' f g = (liftX E g * QuadraticAlgebra.omega -
      algebraMap K _ E'.a₁ * liftX E f - algebraMap K _ E'.a₃) / 2 := by
  apply (eq_div_iff (by norm_num : (2 : FunctionField E) ≠ 0)).mpr
  apply QuadraticAlgebra.ext
  all_goals simp [liftX, liftY]

variable [DecidableEq K]

omit [DecidableEq K] in
/-- The full translated field map represents the actual whole-cubic translation. -/
@[reassoc] theorem translationFieldHom_source :
    Spec.map (CommRingCat.ofHom (translationFieldHom E hQ).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (sourceGenericChart E).toRingHom) ≫
          integralCurveChart E 2 =
      (Spec.map (CommRingCat.ofHom (sourceGenericChart E).toRingHom) ≫
        integralCurveChart E 2) ≫ (affineTranslationIso E (.some u v hQ)).hom := by
  classical
  rw [affineTranslationIso_generic, integralChartPoint, ← Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  change ((translationFieldHom E hQ).comp (sourceGenericChart E)).toRingHom = _
  congr 1
  apply hom_ext
  intro i
  simp only [AlgHom.comp_apply, evaluation_coord]
  fin_cases i
  · change translationFieldHom E hQ (sourceGenericChart E (coord E 2 0)) = translateX E u v
    rw [sourceGenericChart_x, translationFieldHom_liftX, substitution_X]
  · change translationFieldHom E hQ (sourceGenericChart E (coord E 2 1)) = translateY E u v
    rw [sourceGenericChart_y, translationFieldHom_sourceY]
  · change translationFieldHom E hQ (sourceGenericChart E (coord E 2 2)) = 1
    rw [coord_self, map_one, map_one]

variable (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- Translation of the original Vélu ordinate is its original substituted formula. -/
theorem translationFieldHom_veluY :
    translationFieldHom E hQ (liftY E (curve E G) (xFunction E G) (slopeFunction E G)) =
      imageY E G (substitution _ (translateX_transcendental E hQ)) (translateY E u v) := by
  rw [liftY_completed]
  simp only [map_div₀, map_sub, map_mul, map_ofNat, AlgHom.commutes,
    translationFieldHom_omega, translationFieldHom_liftX]
  simp only [imageY, imageX, translationCompletedY, substitution_X]
  rfl

variable [IsAlgClosed K] (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

include hodd

/-- A kernel translation fixes both original generic Vélu functions in the full field. -/
theorem translationFieldHom_velu (hQG : Affine.Point.some u v hQ ∈ G) :
    translationFieldHom E hQ (liftX E (xFunction E G)) = liftX E (xFunction E G) ∧
      translationFieldHom E hQ (liftY E (curve E G) (xFunction E G) (slopeFunction E G)) =
        liftY E (curve E G) (xFunction E G) (slopeFunction E G) := by
  rw [translationFieldHom_liftX, translationFieldHom_veluY]
  exact translated_image_kernel E G hodd hQ hQG

end WeierstrassCurve.Velu

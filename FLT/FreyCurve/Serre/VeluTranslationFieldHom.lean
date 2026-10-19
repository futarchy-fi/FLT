/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluTranslationGenericCoordinates
public import FLT.FreyCurve.Serre.VeluGenericFieldChartComparison

/-!
# The original translation acts on the full quadratic function field

Substitute the original translated x-coordinate and the original completed
y-coordinate. The source equation proves that this is an actual field map.
-/

@[expose] public noncomputable section

open RatFunc

namespace WeierstrassCurve.Velu

variable {K : Type} [Field K] [CharZero K] (E : WeierstrassCurve K) [E.IsElliptic]
  {u v : K} (hQ : E.toAffine.Nonsingular u v)

/-- Original completed y after translation. -/
def translationCompletedY (u v : K) : FunctionField E :=
  2 * translateY E u v + algebraMap K _ E.a₁ * translateX E u v + algebraMap K _ E.a₃

/-- The original translated coordinates satisfy the completed quadratic relation. -/
theorem translationCompletedY_sq :
    translationCompletedY E u v * translationCompletedY E u v =
      substitution _ (translateX_transcendental E hQ) (cubicFunction E) := by
  have h := (translate_nonsingular E hQ).1
  rw [Affine.equation_iff] at h
  have hc := congrArg (substitution _ (translateX_transcendental E hQ)) (cubicFunction_eq E)
  rw [hc]
  have hC (c : K) : substitution _ (translateX_transcendental E hQ) (RatFunc.C c) =
      algebraMap K (FunctionField E) c :=
    (substitution _ (translateX_transcendental E hQ)).commutes c
  simp only [map_add, map_mul, map_pow, map_ofNat, hC, substitution_X]
  dsimp [translationCompletedY, b₂, b₄, b₆, WeierstrassCurve.map] at h ⊢
  simp only [map_add, map_mul, map_pow, map_ofNat] at h ⊢
  linear_combination 4 * h

/-- Translation induces an actual homomorphism on the entire original quadratic field. -/
def translationFieldHom : FunctionField E →ₐ[K] FunctionField E := by
  let σ := substitution _ (translateX_transcendental E hQ)
  let f := @QuadraticAlgebra.lift K⟮X⟯ (cubicFunction E) 0 _
    (FunctionField E) _ σ.toRingHom.toAlgebra
      ⟨translationCompletedY E u v, by
        change translationCompletedY E u v * translationCompletedY E u v =
          σ (cubicFunction E) * 1 + σ 0 * translationCompletedY E u v
        simpa only [map_zero, zero_mul, add_zero, mul_one] using
          translationCompletedY_sq E hQ⟩
  refine { (@AlgHom.toRingHom K⟮X⟯ (FunctionField E) (FunctionField E)
    _ _ _ _ σ.toRingHom.toAlgebra f) with commutes' := fun c ↦ ?_ }
  change σ (RatFunc.C c) * 1 + σ 0 * translationCompletedY E u v = _
  rw [map_zero, zero_mul, add_zero, mul_one]
  exact σ.commutes c

/-- The translated full field map retains both original rational components. -/
theorem translationFieldHom_apply (z : FunctionField E) :
    translationFieldHom E hQ z =
      substitution _ (translateX_transcendental E hQ) z.re +
        substitution _ (translateX_transcendental E hQ) z.im * translationCompletedY E u v := by
  change substitution _ (translateX_transcendental E hQ) z.re * 1 +
    substitution _ (translateX_transcendental E hQ) z.im * translationCompletedY E u v = _
  rw [mul_one]

/-- The original completed generator has the specified translated value. -/
@[simp] theorem translationFieldHom_omega :
    translationFieldHom E hQ QuadraticAlgebra.omega = translationCompletedY E u v := by
  rw [translationFieldHom_apply]
  simp

/-- The full map restricts to the original rational x substitution. -/
@[simp] theorem translationFieldHom_liftX (f : K⟮X⟯) :
    translationFieldHom E hQ (liftX E f) =
      substitution _ (translateX_transcendental E hQ) f := by
  rw [translationFieldHom_apply]
  simp [liftX, QuadraticAlgebra.algebraMap_eq]

end WeierstrassCurve.Velu

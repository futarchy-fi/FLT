/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineNormalForm
public import FLT.Mazur.WeierstrassAffineProduct

/-!
# Coefficient comparison for triangular maps of original affine cubics

Reducing the pulled-back cubic by the source monic quadratic gives a unique
polynomial pair. Its six coefficients vanish over arbitrary coefficient rings.
-/

@[expose] public noncomputable section

open Polynomial WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W V : WeierstrassCurve R)

/-- All six coefficient relations forced by a triangular map of affine cubics. -/
theorem triangular_coordinate_relations
    (f : Coordinate V 2 →ₐ[R] Coordinate W 2) (r s t v w : R)
    (hx : f (coord V 2 0) = algebraMap R _ r + algebraMap R _ s * coord W 2 0)
    (hy : f (coord V 2 1) = algebraMap R _ t + algebraMap R _ v * coord W 2 0 +
      algebraMap R _ w * coord W 2 1) :
    w ^ 2 = s ^ 3 ∧
    2 * v * w + V.a₁ * s * w - w ^ 2 * W.a₁ = 0 ∧
    2 * t * w + V.a₁ * r * w + V.a₃ * w - w ^ 2 * W.a₃ = 0 ∧
    v ^ 2 + V.a₁ * s * v - 3 * r * s ^ 2 - V.a₂ * s ^ 2 + w ^ 2 * W.a₂ = 0 ∧
    2 * t * v + V.a₁ * (r * v + s * t) + V.a₃ * v - 3 * r ^ 2 * s -
      2 * V.a₂ * r * s - V.a₄ * s + w ^ 2 * W.a₄ = 0 ∧
    t ^ 2 + (V.a₁ * r + V.a₃) * t - r ^ 3 - V.a₂ * r ^ 2 - V.a₄ * r - V.a₆ +
      w ^ 2 * W.a₆ = 0 := by
  let c₀ := t ^ 2 + (V.a₁ * r + V.a₃) * t - r ^ 3 - V.a₂ * r ^ 2 - V.a₄ * r -
    V.a₆ + w ^ 2 * W.a₆
  let c₁ := 2 * t * v + V.a₁ * (r * v + s * t) + V.a₃ * v - 3 * r ^ 2 * s -
    2 * V.a₂ * r * s - V.a₄ * s + w ^ 2 * W.a₄
  let c₂ := v ^ 2 + V.a₁ * s * v - 3 * r * s ^ 2 - V.a₂ * s ^ 2 + w ^ 2 * W.a₂
  let d₀ := 2 * t * w + V.a₁ * r * w + V.a₃ * w - w ^ 2 * W.a₃
  let d₁ := 2 * v * w + V.a₁ * s * w - w ^ 2 * W.a₁
  have hV := affine_equation_of_hom V f
  have hW := affine_equation_of_hom W (AlgHom.id R (Coordinate W 2))
  rw [Affine.equation_iff, hx, hy] at hV
  rw [Affine.equation_iff] at hW
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, AlgHom.id_apply] at hV hW
  have hn : affineNormalForm W
      (C c₀ + C c₁ * X + C c₂ * X ^ 2 + C (w ^ 2 - s ^ 3) * X ^ 3)
      (C d₀ + C d₁ * X) = 0 := by
    simp only [affineNormalForm, map_add, map_mul, map_pow, aeval_C, aeval_X,
      c₀, c₁, c₂, d₀, d₁, map_sub, map_ofNat]
    linear_combination hV - (algebraMap R (Coordinate W 2) w) ^ 2 * hW
  obtain ⟨hp, hq⟩ := (affineNormalForm_eq_zero W _ _).mp hn
  have hp₀ := congrArg (fun p : R[X] => p.coeff 0) hp
  have hp₁ := congrArg (fun p : R[X] => p.coeff 1) hp
  have hp₂ := congrArg (fun p : R[X] => p.coeff 2) hp
  have hp₃ := congrArg (fun p : R[X] => p.coeff 3) hp
  have hq₀ := congrArg (fun p : R[X] => p.coeff 0) hq
  have hq₁ := congrArg (fun p : R[X] => p.coeff 1) hq
  norm_num only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero,
    mul_ite, mul_one, mul_zero, ite_true, ite_false, add_zero, zero_add] at hp₀ hp₁ hp₂ hp₃ hq₀ hq₁
  exact ⟨sub_eq_zero.mp hp₃, hq₁, hq₀, hp₂, hp₁, hp₀⟩

end FLT.Mazur.WeierstrassIntegralChart

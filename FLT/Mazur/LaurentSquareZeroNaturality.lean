/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentSquareZeroCoordinate
public import FLT.Mazur.LaurentScaledEvaluationCoefficients

/-!
# Naturality and universal coordinates for square-zero changes

Every ring homomorphism transports the explicit coordinate change. Evaluating
at the universal Laurent unit is exactly coefficient change, so the universal
point describes the full Laurent polynomial, including nilpotent coefficients.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentSquareZeroCoordinate
open LaurentPolynomial LaurentPairNaturality LaurentScaledEvaluationCoefficients
open PolygonChartScaling PolygonScalingNaturality LaurentCoefficientEvaluation
variable {R B D : Type*} [CommRing R] [CommRing B] [CommRing D]

/-- A coefficient-ring map transports a specified square-zero Laurent coordinate change. -/
theorem change_map (f : R →+* B) (g : B →+* D) (e : B) (he : e ^ 2 = 0)
    (q : R[T;T⁻¹]) (u : Bˣ) :
    Units.map g (change f e he q u) =
      change (g.comp f) (g e) (by rw [← map_pow, he, map_zero]) q (Units.map g u) := by
  apply Units.ext
  change g (u.val + e * eval₂ f u q) =
    g u.val + g e * eval₂ (g.comp f) (Units.map g u) q
  rw [map_add, map_mul]
  congr 2
  exact congrArg (fun F : R[T;T⁻¹] →+* D ↦ F q) (eval₂_map f g u)

/-- The universal coordinate evaluates a Laurent polynomial by mapping its coefficients. -/
theorem eval₂_coordinate_one (f : R →+* B) (q : R[T;T⁻¹]) :
    eval₂ (C.comp f) (coordinateUnit (1 : Bˣ)) q = coeffMap f q := by
  ext d
  rw [eval₂_scaled_coeff, coeffMap_coeff]
  simp only [one_zpow, Units.val_one, mul_one]

/-- The universal value of a coordinate change is its full coefficientwise expression. -/
theorem change_coordinate_one_val (f : R →+* B) (e : B) (he : e ^ 2 = 0)
    (q : R[T;T⁻¹]) :
    (change (C.comp f) (C e) (by rw [← map_pow, he, map_zero]) q
      (coordinateUnit (1 : Bˣ))).val = T 1 + C e * coeffMap f q := by
  rw [change_val, eval₂_coordinate_one]
  simp only [coordinateUnit, Units.val_one, map_one, one_mul]

end FLT.Mazur.LaurentSquareZeroCoordinate

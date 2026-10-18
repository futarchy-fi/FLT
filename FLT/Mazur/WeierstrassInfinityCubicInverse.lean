/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityFactorRatioParameter

/-!
# Solving the full infinity cubic with a fixed horizontal coordinate

When the linear tangent factor is a unit, finite nilpotent iteration constructs
the vertical coordinate. Uniqueness holds in the entire coefficient algebra.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassIntegralChart
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R) (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∈ I) (h6 : W.a₆ ∈ I)
  (x : A)
local notation "c" => algebraMap R A
local notation "J" => I.map c

/-- The nonlinear part of the original cubic, as a polynomial in Z/Y. -/
def infinityVerticalCorrection : A[X] :=
  C (c W.a₃) * X ^ 2 - C (c W.a₂ * x ^ 2) * X -
    C (c W.a₄ * x) * X ^ 2 - C (c W.a₆) * X ^ 3

include h2 h3 h4 h6 in
/-- All correction coefficients lie in the extended nilpotent ideal. -/
theorem infinityVerticalCorrection_mem : infinityVerticalCorrection W x ∈ (J).map C := by
  apply ((J).map C).sub_mem
  · apply ((J).map C).sub_mem
    · apply ((J).map C).sub_mem
      · exact ((J).map C).mul_mem_right _
          (Ideal.mem_map_of_mem C (Ideal.mem_map_of_mem c h3))
      · exact ((J).map C).mul_mem_right _
          (Ideal.mem_map_of_mem C ((J).mul_mem_right _ (Ideal.mem_map_of_mem c h2)))
    · exact ((J).map C).mul_mem_right _
        (Ideal.mem_map_of_mem C ((J).mul_mem_right _ (Ideal.mem_map_of_mem c h4)))
  · exact ((J).map C).mul_mem_right _
      (Ideal.mem_map_of_mem C (Ideal.mem_map_of_mem c h6))

/-- Evaluation keeps every term of the full cubic. -/
theorem infinityVerticalCorrection_eval (z : A) :
    (1 + c W.a₁ * x) * z + (infinityVerticalCorrection W x).eval z =
      z * (1 + c W.a₁ * x + c W.a₃ * z - c W.a₂ * x ^ 2 -
        c W.a₄ * x * z - c W.a₆ * z ^ 2) := by
  simp only [infinityVerticalCorrection, eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  ring

variable (hx : IsUnit (1 + algebraMap R A W.a₁ * x))

/-- The actual vertical coordinate constructed by finite iteration. -/
def infinityVerticalSolution : A :=
  NilpotentPolynomialInverse.inverse J (infinityVerticalCorrection W x)
    (infinityVerticalCorrection_mem W I h2 h3 h4 h6 x)
    (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI c) _ hx (x ^ 3)

/-- The constructed coordinate solves the untruncated original cubic. -/
theorem infinityVerticalSolution_equation :
    let z := infinityVerticalSolution W I hI h2 h3 h4 h6 x hx
    z * (1 + c W.a₁ * x + c W.a₃ * z - c W.a₂ * x ^ 2 -
      c W.a₄ * x * z - c W.a₆ * z ^ 2) = x ^ 3 := by
  dsimp only
  rw [← infinityVerticalCorrection_eval]
  exact NilpotentPolynomialInverse.inverse_equation J (infinityVerticalCorrection W x)
    (infinityVerticalCorrection_mem W I h2 h3 h4 h6 x)
    (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI c) _ hx (x ^ 3)

include hI h2 h3 h4 h6 hx in
/-- Two full vertical solutions with the same horizontal coordinate coincide. -/
theorem infinityVerticalSolution_unique {z w : A}
    (hz : z * (1 + c W.a₁ * x + c W.a₃ * z - c W.a₂ * x ^ 2 -
      c W.a₄ * x * z - c W.a₆ * z ^ 2) = x ^ 3)
    (hw : w * (1 + c W.a₁ * x + c W.a₃ * w - c W.a₂ * x ^ 2 -
      c W.a₄ * x * w - c W.a₆ * w ^ 2) = x ^ 3) : z = w := by
  apply NilpotentPolynomialInverse.solution_unique J (infinityVerticalCorrection W x)
    (infinityVerticalCorrection_mem W I h2 h3 h4 h6 x)
    (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI c) _ hx (x ^ 3)
  · rwa [infinityVerticalCorrection_eval]
  · rwa [infinityVerticalCorrection_eval]

end FLT.Mazur.WeierstrassIntegralChart

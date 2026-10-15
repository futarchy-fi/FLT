/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentCoefficientEvaluation

/-!
# Interchanging the two Laurent inputs

An explicit involution exchanges the two independent units and commutes with
coefficient change. This records symmetry without discarding nilpotents.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentPairSwap
open LaurentPolynomial PolygonScalingNaturality LaurentCoefficientEvaluation
variable (R : Type*) [CommRing R]

/-- Exchange the inner and outer Laurent variables. -/
def swap : R[T;T⁻¹][T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹] :=
  eval₂ (coeffMap (C : R →+* R[T;T⁻¹]))
    (Units.map (C : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹])
      (PolygonChartScaling.coordinateUnit (1 : Rˣ)))

/-- Inner Laurent expressions become outer Laurent expressions. -/
@[simp] theorem swap_C (p : R[T;T⁻¹]) :
    swap R (C p) = coeffMap (C : R →+* R[T;T⁻¹]) p := eval₂_C _ _ _

/-- The outer positive generator becomes the inner positive generator. -/
@[simp] theorem swap_T_one : swap R (T 1) = C (T 1) := by
  simp [swap, PolygonChartScaling.coordinateUnit]

/-- The outer inverse generator becomes the inner inverse generator. -/
@[simp] theorem swap_T_neg_one : swap R (T (-1)) = C (T (-1)) := by
  simp [swap, PolygonChartScaling.coordinateUnit]

/-- Outer Laurent expressions become inner Laurent expressions. -/
@[simp] theorem swap_coeffMap (p : R[T;T⁻¹]) :
    swap R (coeffMap (C : R →+* R[T;T⁻¹]) p) = C p := by
  have he : (swap R).comp (coeffMap (C : R →+* R[T;T⁻¹])) = C := by
    apply ringHom_ext <;> simp
  exact congrArg (fun f : R[T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹] ↦ f p) he

/-- Swapping twice retains the whole Laurent ring, including all coefficient nilpotents. -/
theorem swap_comp_swap : (swap R).comp (swap R) = RingHom.id _ := by
  apply ringHom_ext <;> simp

/-- The explicit exchange is an involution. -/
@[simp] theorem swap_swap (p : R[T;T⁻¹][T;T⁻¹]) : swap R (swap R p) = p :=
  congrArg (fun f : R[T;T⁻¹][T;T⁻¹] →+* R[T;T⁻¹][T;T⁻¹] ↦ f p) (swap_comp_swap R)

/-- Swapping preserves the product coordinate of ordinary Laurent multiplication. -/
@[simp] theorem swap_product : swap R (C (T 1) * T 1) = C (T 1) * T 1 := by
  rw [map_mul, swap_C, coeffMap_T_one, swap_T_one, mul_comm]

/-- Exchanging inputs commutes with every change of the coefficient ring. -/
theorem swap_natural {S : Type*} [CommRing S] (f : R →+* S) :
    (swap S).comp (coeffMap (coeffMap f)) =
      (coeffMap (coeffMap f)).comp (swap R) := by
  apply ringHom_ext
  · intro p
    simp only [RingHom.comp_apply, coeffMap_C, swap_C]
    have he : (coeffMap (C : S →+* S[T;T⁻¹])).comp (coeffMap f) =
        (coeffMap (coeffMap f)).comp (coeffMap (C : R →+* R[T;T⁻¹])) := by
      apply ringHom_ext <;> simp
    exact congrArg (fun g : R[T;T⁻¹] →+* S[T;T⁻¹][T;T⁻¹] ↦ g p) he
  · simp
  · simp

end FLT.Mazur.LaurentPairSwap

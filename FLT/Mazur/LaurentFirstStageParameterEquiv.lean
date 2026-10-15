/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentFirstStageParameter

/-!
# Moving the universal parameter is an isomorphism of the original rings

The retained-parameter evaluation has an explicit inverse. Thus passing
between the two orders of Laurent extension and first-order truncation
retains the complete coefficient rings, including their nilpotent layers.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentFirstStageParameter
open LaurentPolynomial PolygonInfinitesimalStages PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
variable (R : Type) [CommRing R]
local notation "A" => Ring R 1
local notation "S" => Ring R[T;T⁻¹] 1

/-- The inverse keeps the Laurent variable and sends the parameter to the original parameter. -/
def parameterUneval : (S) →+* (A)[T;T⁻¹] :=
  AdjoinRoot.lift (coeffMap (algebraMap R (A))) (C (parameter R 1)) (by
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_X, ← map_pow, parameter_pow, map_zero])

/-- The inverse carries every Laurent coefficient to its unchanged scalar lift. -/
theorem parameterUneval_scalar (p : R[T;T⁻¹]) :
    parameterUneval R (algebraMap R[T;T⁻¹] (S) p) =
      coeffMap (algebraMap R (A)) p := AdjoinRoot.lift_of _

/-- The inverse retains the actual first-order smoothing parameter. -/
theorem parameterUneval_parameter :
    parameterUneval R (parameter R[T;T⁻¹] 1) = C (parameter R 1) :=
  AdjoinRoot.lift_root _

/-- The original truncated coefficient map is retained by the inverse. -/
theorem parameterUneval_stage :
    (parameterUneval R).comp (stageCoefficientMap (C : R →+* R[T;T⁻¹]) 1) =
      (C : (A) →+* (A)[T;T⁻¹]) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro r
    change parameterUneval R (stageCoefficientMap C 1 (algebraMap R (A) r)) = _
    rw [stageCoefficientMap_constant, parameterUneval_scalar, coeffMap_C]
    rfl
  · change parameterUneval R (stageCoefficientMap C 1 (parameter R 1)) = _
    rw [stageCoefficientMap_parameter, parameterUneval_parameter]
    rfl

/-- Evaluating after the inverse fixes the full ring, rather than only its reduction. -/
theorem parameterEval_comp_uneval :
    (parameterEval R).comp (parameterUneval R) = RingHom.id (S) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro p
    change parameterEval R (parameterUneval R (algebraMap R[T;T⁻¹] (S) p)) = _
    rw [parameterUneval_scalar]
    exact DFunLike.congr_fun (parameterEval_lift R) p
  · change parameterEval R (parameterUneval R (parameter R[T;T⁻¹] 1)) = _
    rw [parameterUneval_parameter, parameterEval_parameter]
    rfl

/-- The inverse fixes the original Laurent coefficient ring on every Laurent polynomial. -/
theorem parameterUneval_comp_eval :
    (parameterUneval R).comp (parameterEval R) = RingHom.id (A)[T;T⁻¹] := by
  apply ringHom_ext
  · intro r
    change parameterUneval R (parameterEval R (C r)) = C r
    rw [parameterEval_C]
    exact DFunLike.congr_fun (parameterUneval_stage R) r
  · change parameterUneval R (parameterEval R (T 1)) = T 1
    rw [parameterEval_T_one]
    change parameterUneval R (algebraMap R[T;T⁻¹] (S) (C (1 : R) * T 1)) = _
    rw [map_one, one_mul, parameterUneval_scalar, coeffMap_T_one]
  · change parameterUneval R (parameterEval R (T (-1))) = T (-1)
    rw [parameterEval, eval₂_T, zpow_neg_one]
    change parameterUneval R
      (algebraMap R[T;T⁻¹] (S) (C (↑((1 : Rˣ)⁻¹) : R) * T (-1))) = _
    simp only [inv_one, Units.val_one, map_one, one_mul]
    rw [parameterUneval_scalar, coeffMap_T_neg_one]

/-- The actual retained-parameter evaluation is an isomorphism with its full inverse. -/
def parameterEquiv : (A)[T;T⁻¹] ≃+* (S) where
  __ := parameterEval R
  invFun := parameterUneval R
  left_inv p := DFunLike.congr_fun (parameterUneval_comp_eval R) p
  right_inv s := DFunLike.congr_fun (parameterEval_comp_uneval R) s

/-- The isomorphism's forward map is exactly the evaluation already used by the action. -/
theorem parameterEquiv_toRingHom : (parameterEquiv R).toRingHom = parameterEval R := rfl

/-- Its inverse is the unchanged Laurent-valued truncated coefficient map. -/
theorem parameterEquiv_symm_toRingHom :
    (parameterEquiv R).symm.toRingHom = parameterUneval R := rfl

end FLT.Mazur.LaurentFirstStageParameter

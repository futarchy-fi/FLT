/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentStageParameter

/-!
# Moving the universal parameter is an isomorphism of the original rings

The retained-parameter evaluation has an explicit inverse. Thus passing
between the two orders of Laurent extension and arbitrary-stage truncation
retains the complete coefficient rings, including their nilpotent layers.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentStageParameter
open LaurentPolynomial PolygonInfinitesimalStages PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
variable (R : Type) [CommRing R] (m : ℕ)
local notation "A" => Ring R m
local notation "S" => Ring R[T;T⁻¹] m

/-- The inverse keeps the Laurent variable and sends the parameter to the original parameter. -/
def parameterUneval : (S) →+* (A)[T;T⁻¹] :=
  AdjoinRoot.lift (coeffMap (algebraMap R (A))) (C (parameter R m)) (by
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_X, ← map_pow, parameter_pow, map_zero])

/-- The inverse carries every Laurent coefficient to its unchanged scalar lift. -/
theorem parameterUneval_scalar (p : R[T;T⁻¹]) :
    parameterUneval R m (algebraMap R[T;T⁻¹] (S) p) =
      coeffMap (algebraMap R (A)) p := AdjoinRoot.lift_of _

/-- The inverse retains the actual arbitrary-stage smoothing parameter. -/
theorem parameterUneval_parameter :
    parameterUneval R m (parameter R[T;T⁻¹] m) = C (parameter R m) :=
  AdjoinRoot.lift_root _

/-- The original truncated coefficient map is retained by the inverse. -/
theorem parameterUneval_stage :
    (parameterUneval R m).comp (stageCoefficientMap (C : R →+* R[T;T⁻¹]) m) =
      (C : (A) →+* (A)[T;T⁻¹]) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro r
    change parameterUneval R m (stageCoefficientMap C m (algebraMap R (A) r)) = _
    rw [stageCoefficientMap_constant, parameterUneval_scalar, coeffMap_C]
    rfl
  · change parameterUneval R m (stageCoefficientMap C m (parameter R m)) = _
    rw [stageCoefficientMap_parameter, parameterUneval_parameter]
    rfl

/-- Evaluating after the inverse fixes the full ring, rather than only its reduction. -/
theorem parameterEval_comp_uneval :
    (parameterEval R m).comp (parameterUneval R m) = RingHom.id (S) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro p
    change parameterEval R m (parameterUneval R m (algebraMap R[T;T⁻¹] (S) p)) = _
    rw [parameterUneval_scalar]
    exact DFunLike.congr_fun (parameterEval_lift R m) p
  · change parameterEval R m (parameterUneval R m (parameter R[T;T⁻¹] m)) = _
    rw [parameterUneval_parameter, parameterEval_parameter]
    rfl

/-- The inverse fixes the original Laurent coefficient ring on every Laurent polynomial. -/
theorem parameterUneval_comp_eval :
    (parameterUneval R m).comp (parameterEval R m) = RingHom.id (A)[T;T⁻¹] := by
  apply ringHom_ext
  · intro r
    change parameterUneval R m (parameterEval R m (C r)) = C r
    rw [parameterEval_C]
    exact DFunLike.congr_fun (parameterUneval_stage R m) r
  · change parameterUneval R m (parameterEval R m (T 1)) = T 1
    rw [parameterEval_T_one]
    change parameterUneval R m (algebraMap R[T;T⁻¹] (S) (C (1 : R) * T 1)) = _
    rw [map_one, one_mul, parameterUneval_scalar, coeffMap_T_one]
  · change parameterUneval R m (parameterEval R m (T (-1))) = T (-1)
    rw [parameterEval, eval₂_T, zpow_neg_one]
    change parameterUneval R m
      (algebraMap R[T;T⁻¹] (S) (C (↑((1 : Rˣ)⁻¹) : R) * T (-1))) = _
    simp only [inv_one, Units.val_one, map_one, one_mul]
    rw [parameterUneval_scalar, coeffMap_T_neg_one]

/-- The actual retained-parameter evaluation is an isomorphism with its full inverse. -/
def parameterEquiv : (A)[T;T⁻¹] ≃+* (S) where
  __ := parameterEval R m
  invFun := parameterUneval R m
  left_inv p := DFunLike.congr_fun (parameterUneval_comp_eval R m) p
  right_inv s := DFunLike.congr_fun (parameterEval_comp_uneval R m) s

/-- The isomorphism's forward map is exactly the evaluation already used by the action. -/
theorem parameterEquiv_toRingHom : (parameterEquiv R m).toRingHom = parameterEval R m := rfl

/-- Its inverse is the unchanged Laurent-valued truncated coefficient map. -/
theorem parameterEquiv_symm_toRingHom :
    (parameterEquiv R m).symm.toRingHom = parameterUneval R m := rfl

end FLT.Mazur.LaurentStageParameter

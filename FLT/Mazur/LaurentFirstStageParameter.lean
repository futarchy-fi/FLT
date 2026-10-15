/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentSquareZeroNaturality
public import FLT.Mazur.PolygonStageCoefficientChange

/-!
# Moving the universal action parameter into the first-stage coefficient ring

Evaluation of the first Laurent variable in the stage over R[T,T⁻¹]
retains the entire variable and every smoothing coefficient. On lifted
reduced polynomials it is exactly the original scalar inclusion.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.LaurentFirstStageParameter
open LaurentPolynomial PolygonInfinitesimalStages PolygonChartScaling
open PolygonScalingNaturality LaurentPairNaturality
variable (R : Type) [CommRing R]

/-- The original universal first parameter, lifted to the full first-stage coefficient ring. -/
def parameterUnit : (Ring R[T;T⁻¹] 1)ˣ :=
  Units.map (algebraMap R[T;T⁻¹] (Ring R[T;T⁻¹] 1)).toMonoidHom (coordinateUnit 1)

/-- Evaluate the first variable as a coefficient while retaining the smoothing parameter. -/
def parameterEval : (Ring R 1)[T;T⁻¹] →+* Ring R[T;T⁻¹] 1 :=
  eval₂ (stageCoefficientMap C 1) (parameterUnit R)

/-- Smoothing scalars use the specified coefficient change. -/
theorem parameterEval_C (s : Ring R 1) :
    parameterEval R (C s) = stageCoefficientMap C 1 s := eval₂_C ..

/-- The original smoothing parameter is retained exactly. -/
theorem parameterEval_parameter :
    parameterEval R (C (parameter R 1)) = parameter R[T;T⁻¹] 1 := by
  rw [parameterEval_C, stageCoefficientMap_parameter]

/-- Every reduced Laurent polynomial is retained, not specialized to a numerical parameter. -/
theorem parameterEval_lift :
    (parameterEval R).comp (coeffMap (algebraMap R (Ring R 1))) =
      algebraMap R[T;T⁻¹] (Ring R[T;T⁻¹] 1) := by
  rw [parameterEval, eval₂_coeffMap, stageCoefficientMap_comp_scalar]
  rw [parameterUnit, ← eval₂_map]
  change (algebraMap R[T;T⁻¹] (Ring R[T;T⁻¹] 1)).comp
    (PolygonChartScaling.laurent (1 : Rˣ)) = _
  rw [laurent_one, RingHom.comp_id]

/-- The first Laurent coordinate becomes the actual universal coefficient unit. -/
theorem parameterEval_T_one : parameterEval R (T 1) = (parameterUnit R).val := by
  rw [parameterEval, eval₂_T, zpow_one]

/-- Both variables are retained when the first becomes a coefficient. -/
theorem parameterEval_doubleLift (p : R[T;T⁻¹][T;T⁻¹]) :
    coeffMap (parameterEval R) (coeffMap (coeffMap (algebraMap R (Ring R 1))) p) =
      coeffMap (algebraMap R[T;T⁻¹] (Ring R[T;T⁻¹] 1)) p := by
  rw [← RingHom.comp_apply, ← coeffMap_comp, parameterEval_lift]

/-- This coefficient substitution is the original two-variable evaluation on universal inputs. -/
theorem parameterEval_pair :
    pairEval₂ (C.comp (stageCoefficientMap (C : R →+* R[T;T⁻¹]) 1))
      (Units.map (C : Ring R[T;T⁻¹] 1 →+* (Ring R[T;T⁻¹] 1)[T;T⁻¹]).toMonoidHom
        (parameterUnit R)) (coordinateUnit 1) = coeffMap (parameterEval R) := by
  rw [pairEval₂, ← eval₂_map]
  exact RingHom.ext (LaurentSquareZeroCoordinate.eval₂_coordinate_one (parameterEval R))

end FLT.Mazur.LaurentFirstStageParameter

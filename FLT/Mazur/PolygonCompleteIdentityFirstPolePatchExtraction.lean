/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPolePatchMaps
public import FLT.Mazur.NodePoleSecant

/-!
# Coordinate-error extraction on the actual original action patch

Both original pole maps satisfy the same extraction equation with the same
unit coefficient. Subtracting gives an exact equation for the unchanged
ambient outgoing-coordinate error. Pole-function errors remain explicit.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
/-- Cache the actual common patch ring for the mapped extraction identities. -/
local instance polePatchCommRing : CommRing (CompleteIdentityFirstPolePatch K n h U) :=
  inferInstance
attribute [local irreducible] completeIdentityFirstPoleTargetMap completeIdentityFirstPoleSourceMap
  completeIdentityFirstPoleTarget completeIdentityFirstPoleSource
local notation "t" => parameter K 1
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
local notation "ρ" => algebraMap (Ring K 1) (ChartRing (t))
local notation "Q" => completeIdentityFirstPoleTargetMap K n h U
local notation "S" => completeIdentityFirstPoleSourceMap K n h U
local notation "λ" => (completePointStageCommonMarkingUnit K n h 1 (0 : Fin n) : Ring K 1)
local notation "P₂" => leftLaurentMap (t)
  (completePointStagePoleTwoChartNumerator K n h 1 (0 : Fin n) 0)
local notation "P₃" => leftLaurentMap (t)
  (completePointStagePoleThreeChartNumerator K n h 1 (0 : Fin n) 0)
local notation "A" => (η) ((ρ) (AddMonoidAlgebra.coeff (P₂) 2))
local notation "B" => (η) ((ρ) (AddMonoidAlgebra.coeff (P₃) 3))
local notation "C₀" => (η) ((ρ) (AddMonoidAlgebra.coeff (P₃) 2 +
  3 * AddMonoidAlgebra.coeff (P₃) 3))
local notation "a" => (η) ((ρ) ((λ) ^ 2))
local notation "v" => (η) ((ρ) ((λ) ^ 5))
local notation "f₂" => completePointNodeLocalizedPoleTwo K n h 1 (0 : Fin n) 0
local notation "f₃" => completePointNodeLocalizedPoleThree K n h 1 (0 : Fin n) 0
local notation "x" => (η) (leftCoordinate (t))

/-- The retained pole combination uses the actual lower coefficients and common marking unit. -/
def completeIdentityFirstPoleCombination : StageNodeLocalization K 1 :=
  (a) * ((f₃) - (B)) - (C₀) * ((f₂) - (A))
local notation "F" => completeIdentityFirstPoleCombination K n h

/-- Extraction along the actual target, on the original common patch. -/
theorem completeIdentityFirstPolePatch_target_extract :
    ((Q) (x) - 1) ^ 3 * (Q) (F) = (Q) (v) * (Q) (x) := by
  simpa only [completeIdentityFirstPoleCombination,
    (Q).map_mul, (Q).map_pow, (Q).map_sub, (Q).map_one] using
    congrArg (Q) (completePointFirstNodePoles_extract_left K n h 0)

/-- The scaled source retains exactly the same extraction coefficient as the target. -/
theorem completeIdentityFirstPolePatch_source_extract :
    ((S) (x) - 1) ^ 3 * (S) (F) = (Q) (v) * (S) (x) := by
  rw [completeIdentityFirstPolePatch_coefficients]
  simpa only [completeIdentityFirstPoleCombination,
    (S).map_mul, (S).map_pow, (S).map_sub, (S).map_one] using
    congrArg (S) (completePointFirstNodePoles_extract_left K n h 0)

/-- The pole-combination error retains only differences of the actual pole functions. -/
theorem completeIdentityFirstPolePatch_combination_error :
    (Q) (F) - (S) (F) =
      (Q) (a) * ((Q) (f₃) - (S) (f₃)) - (Q) (C₀) * ((Q) (f₂) - (S) (f₂)) := by
  simp only [completeIdentityFirstPoleCombination,
    (Q).map_sub, (Q).map_mul, (S).map_sub, (S).map_mul]
  simp only [← completeIdentityFirstPolePatch_coefficients K n h U]
  ring

/-- The exact secant coefficient for the original outgoing-coordinate error. -/
def completeIdentityFirstPoleSecantCoefficient : CompleteIdentityFirstPolePatch K n h U :=
  (Q) (v) - NodePoleSecant.cubic ((Q) (x)) ((S) (x)) * (S) (F)

/-- The original ambient coordinate error satisfies the actual pole secant equation. -/
theorem completeIdentityFirstPolePatch_error_equation :
    completeIdentityFirstPoleSecantCoefficient K n h U *
        ((Q) (x) - (S) (x)) = ((Q) (x) - 1) ^ 3 *
          ((Q) (a) * ((Q) (f₃) - (S) (f₃)) -
            (Q) (C₀) * ((Q) (f₂) - (S) (f₂))) := by
  rw [← completeIdentityFirstPolePatch_combination_error]
  exact NodePoleSecant.equation _ _ _ _ _
    (completeIdentityFirstPolePatch_target_extract K n h U)
    (completeIdentityFirstPolePatch_source_extract K n h U)

end FLT.Mazur.PolygonInfinitesimalStages

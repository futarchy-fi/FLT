/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstSourcePoleGeometry

/-!
# Original target functions on the source-only localization

The actual target homomorphism retains its original coefficients and
ambient errors without any target denominator being inverted.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentFirstStageParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "b" => ringMap (stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1)
  (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K)

local notation "s" => completeIdentityFirstPoleSource K n h U
local notation "d" => nodeMarkingDenominator (t)

local notation "Z" => CompleteIdentityFirstSourcePolePatch K n h U
local notation "ι" => algebraMap Γ((R), (V).1) (Z)
local notation "q" => completeIdentityFirstPoleTarget K n h U
local notation "S" => completeIdentityFirstSourcePoleFunctions K n h U
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)
local notation "M" => completeIdentityFirstSourcePolePatchMap K n h U
local notation "p" => (pullback.snd _ _ : (R) ⟶ chart (Ring K 1) (t))

/-- The original target functions require only the source localization. -/
def completeIdentityFirstSourcePoleTargetFunctions : ChartRing (t) →+* (Z) :=
  (ι).comp (q)
local notation "Q" => completeIdentityFirstSourcePoleTargetFunctions K n h U

/-- These are the functions of the original target projection. -/
@[reassoc] theorem completeIdentityFirstSourcePoleTargetFunctions_map :
    Spec.map (CommRingCat.ofHom (Q)) = (M) ≫ (V).1.ι ≫ (p) := by
  rw [completeIdentityFirstSourcePolePatchMap,
    AffineOpenSpectrumFunctions.map_comp_inclusion]
  rfl

/-- Source and target retain precisely the same original coefficient map. -/
theorem completeIdentityFirstSourcePoleTargetFunctions_coefficients (a : Ring K 1) :
    (Q) (algebraMap (Ring K 1) (ChartRing (t)) a) =
      (S) ((η) (algebraMap (Ring K 1) (ChartRing (t)) a)) := by
  rw [completeIdentityFirstSourcePoleFunctions_algebraMap]
  apply congrArg (ι)
  dsimp only [completeIdentityFirstPoleTarget, completeIdentityFirstPoleSource,
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [ringMap_scalar, AlgHom.commutes]
  exact congrArg (ρ) (completeIdentityFirstNodePolynomialMap_coefficients K n h a).symm

/-- The difference is the unchanged original ambient error. -/
theorem completeIdentityFirstSourcePoleTargetFunctions_error (z : ChartRing (t)) :
    (Q) z - (S) ((η) z) =
      (ι) ((ρ) (completeIdentityFirstAmbientError K n h z)) := by
  rw [completeIdentityFirstSourcePoleFunctions_algebraMap]
  simp only [completeIdentityFirstSourcePoleTargetFunctions, completeIdentityFirstPoleTarget,
    completeIdentityFirstPoleSource, completeIdentityFirstAmbientError, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub]

end FLT.Mazur.PolygonInfinitesimalStages

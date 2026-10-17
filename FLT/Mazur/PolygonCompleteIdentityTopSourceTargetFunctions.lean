/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopSourcePoleGeometry

/-!
# Original target functions on the source-only localization

The actual target homomorphism retains its original coefficients and
ambient errors without any target denominator being inverted.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentStageParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h (m + 1) 0 0).toScheme.affineOpens)
local notation "t" => parameter K (m + 1)
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h (m + 1) 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "ρ" => completeIdentityTopAmbientRestriction K n h m (V)
local notation "b" => ringMap (stageCoefficientMap (C : K →+* K[T;T⁻¹]) (m + 1))
  (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K (m + 1))

local notation "s" => completeIdentityTopPoleSource K n h m U
local notation "d" => nodeMarkingDenominator (t)

local notation "Z" => CompleteIdentityTopSourcePolePatch K n h m U
local notation "ι" => algebraMap Γ((R), (V).1) (Z)
local notation "q" => completeIdentityTopPoleTarget K n h m U
local notation "S" => completeIdentityTopSourcePoleFunctions K n h m U
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K (m + 1))
local notation "M" => completeIdentityTopSourcePolePatchMap K n h m U
local notation "p" => (pullback.snd _ _ : (R) ⟶ chart (Ring K (m + 1)) (t))

/-- The original target functions require only the source localization. -/
def completeIdentityTopSourcePoleTargetFunctions : ChartRing (t) →+* (Z) :=
  (ι).comp (q)
local notation "Q" => completeIdentityTopSourcePoleTargetFunctions K n h m U

/-- These are the functions of the original target projection. -/
@[reassoc] theorem completeIdentityTopSourcePoleTargetFunctions_map :
    Spec.map (CommRingCat.ofHom (Q)) = (M) ≫ (V).1.ι ≫ (p) := by
  rw [completeIdentityTopSourcePolePatchMap,
    AffineOpenSpectrumFunctions.map_comp_inclusion]
  rfl

/-- Source and target retain precisely the same original coefficient map. -/
theorem completeIdentityTopSourcePoleTargetFunctions_coefficients (a : Ring K (m + 1)) :
    (Q) (algebraMap (Ring K (m + 1)) (ChartRing (t)) a) =
      (S) ((η) (algebraMap (Ring K (m + 1)) (ChartRing (t)) a)) := by
  rw [completeIdentityTopSourcePoleFunctions_algebraMap]
  apply congrArg (ι)
  dsimp only [completeIdentityTopPoleTarget, completeIdentityTopPoleSource,
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [ringMap_scalar, AlgHom.commutes]
  exact congrArg (ρ) (completeIdentityTopNodePolynomialMap_coefficients K n h m a).symm

/-- The difference is the unchanged original ambient error. -/
theorem completeIdentityTopSourcePoleTargetFunctions_error (z : ChartRing (t)) :
    (Q) z - (S) ((η) z) =
      (ι) ((ρ) (completeIdentityTopAmbientError K n h m z)) := by
  rw [completeIdentityTopSourcePoleFunctions_algebraMap]
  simp only [completeIdentityTopSourcePoleTargetFunctions, completeIdentityTopPoleTarget,
    completeIdentityTopPoleSource, completeIdentityTopAmbientError, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub]

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PairedAwayLocalization
public import FLT.Mazur.PolygonCompleteIdentityTopNodePolynomials
public import FLT.Mazur.PolygonCompleteIdentityAdicAmbientLifts
public import FLT.Mazur.PolygonCompleteIdentityTopChartAmbientErrors
public import FLT.Mazur.PolygonCompleteIdentityTopChartLocalEquations
public import FLT.Mazur.PolygonCompletePointNodePoleEquations

/-!
# Original source and target pole maps on the same complete-action patch

Restrict the actual target and reciprocally scaled source to an original
affine patch, then invert their two marking denominators together. The maps
retain the original coefficient homomorphism and the original ambient errors.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
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

/-- The actual target restricted to the original affine patch. -/
def completeIdentityTopPoleTarget : ChartRing (t) →+* Γ((R), (V).1) :=
  (ρ).hom.comp (completeIdentityTopAmbientTargetFunctions K n h m)

/-- The unchanged reciprocal source on precisely the same affine patch. -/
def completeIdentityTopPoleSource : ChartRing (t) →+* Γ((R), (V).1) :=
  (ρ).hom.comp ((completeIdentityTopAmbientSourceFunctions K n h m).comp
    ((σ).toRingHom.comp (b)))
local notation "q" => completeIdentityTopPoleTarget K n h m U
local notation "s" => completeIdentityTopPoleSource K n h m U
local notation "d" => nodeMarkingDenominator (t)

/-- The common original patch with both actual marking denominators inverted. -/
abbrev CompleteIdentityTopPolePatch := PairedAwayLocalization.Ring (q) (s) (d)
local notation "Z" => CompleteIdentityTopPolePatch K n h m U
local notation "ι" => algebraMap Γ((R), (V).1) (Z)

/-- The same original localized pole functions pulled back along the actual target. -/
def completeIdentityTopPoleTargetMap : StageNodeLocalization K (m + 1) →+* (Z) :=
  PairedAwayLocalization.first (q) (s) (d)

/-- Those unchanged functions pulled back along the actual scaled source. -/
def completeIdentityTopPoleSourceMap : StageNodeLocalization K (m + 1) →+* (Z) :=
  PairedAwayLocalization.second (q) (s) (d)
local notation "Q" => completeIdentityTopPoleTargetMap K n h m U
local notation "S" => completeIdentityTopPoleSourceMap K n h m U
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K (m + 1))

/-- Every original target numerator retains its actual patch value. -/
theorem completeIdentityTopPoleTargetMap_algebraMap (z : ChartRing (t)) :
    (Q) ((η) z) = (ι) ((q) z) := PairedAwayLocalization.first_algebraMap _ _ _ z

/-- Every scaled source numerator retains its actual patch value. -/
theorem completeIdentityTopPoleSourceMap_algebraMap (z : ChartRing (t)) :
    (S) ((η) z) = (ι) ((s) z) := PairedAwayLocalization.second_algebraMap _ _ _ z

/-- The original base coefficients agree before and after the common localization. -/
theorem completeIdentityTopPolePatch_coefficients (a : Ring K (m + 1)) :
    (Q) ((η) (algebraMap (Ring K (m + 1)) (ChartRing (t)) a)) =
      (S) ((η) (algebraMap (Ring K (m + 1)) (ChartRing (t)) a)) := by
  rw [completeIdentityTopPoleTargetMap_algebraMap,
    completeIdentityTopPoleSourceMap_algebraMap]
  apply congrArg (ι)
  dsimp only [completeIdentityTopPoleTarget, completeIdentityTopPoleSource,
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [ringMap_scalar, AlgHom.commutes]
  exact congrArg (ρ) (completeIdentityTopNodePolynomialMap_coefficients K n h m a).symm

/-- Their difference is exactly the original ambient error on the common patch. -/
theorem completeIdentityTopPolePatch_error (z : ChartRing (t)) :
    (Q) ((η) z) - (S) ((η) z) =
      (ι) ((ρ) (completeIdentityTopAmbientError K n h m z)) := by
  rw [completeIdentityTopPoleTargetMap_algebraMap,
    completeIdentityTopPoleSourceMap_algebraMap]
  simp only [completeIdentityTopPoleTarget, completeIdentityTopPoleSource,
    completeIdentityTopAmbientError, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, map_sub]

end FLT.Mazur.PolygonInfinitesimalStages

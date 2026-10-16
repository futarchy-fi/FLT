/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PairedAwayLocalization
public import FLT.Mazur.PolygonCompleteIdentityFirstNodePolynomials
public import FLT.Mazur.PolygonCompleteIdentityFirstCompleteErrors
public import FLT.Mazur.PolygonCompletePointFirstLocalizedCoordinateExtraction

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

/-- The actual target restricted to the original affine patch. -/
def completeIdentityFirstPoleTarget : ChartRing (t) →+* Γ((R), (V).1) :=
  (ρ).hom.comp (completeIdentityFirstAmbientTargetFunctions K n h)

/-- The unchanged reciprocal source on precisely the same affine patch. -/
def completeIdentityFirstPoleSource : ChartRing (t) →+* Γ((R), (V).1) :=
  (ρ).hom.comp ((completeIdentityFirstAmbientSourceFunctions K n h).comp
    ((σ).toRingHom.comp (b)))
local notation "q" => completeIdentityFirstPoleTarget K n h U
local notation "s" => completeIdentityFirstPoleSource K n h U
local notation "d" => nodeMarkingDenominator (t)

/-- The common original patch with both actual marking denominators inverted. -/
abbrev CompleteIdentityFirstPolePatch := PairedAwayLocalization.Ring (q) (s) (d)
local notation "Z" => CompleteIdentityFirstPolePatch K n h U
local notation "ι" => algebraMap Γ((R), (V).1) (Z)

/-- The same original localized pole functions pulled back along the actual target. -/
def completeIdentityFirstPoleTargetMap : StageNodeLocalization K 1 →+* (Z) :=
  PairedAwayLocalization.first (q) (s) (d)

/-- Those unchanged functions pulled back along the actual scaled source. -/
def completeIdentityFirstPoleSourceMap : StageNodeLocalization K 1 →+* (Z) :=
  PairedAwayLocalization.second (q) (s) (d)
local notation "Q" => completeIdentityFirstPoleTargetMap K n h U
local notation "S" => completeIdentityFirstPoleSourceMap K n h U
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)

/-- Every original target numerator retains its actual patch value. -/
theorem completeIdentityFirstPoleTargetMap_algebraMap (z : ChartRing (t)) :
    (Q) ((η) z) = (ι) ((q) z) := PairedAwayLocalization.first_algebraMap _ _ _ z

/-- Every scaled source numerator retains its actual patch value. -/
theorem completeIdentityFirstPoleSourceMap_algebraMap (z : ChartRing (t)) :
    (S) ((η) z) = (ι) ((s) z) := PairedAwayLocalization.second_algebraMap _ _ _ z

/-- The original base coefficients agree before and after the common localization. -/
theorem completeIdentityFirstPolePatch_coefficients (a : Ring K 1) :
    (Q) ((η) (algebraMap (Ring K 1) (ChartRing (t)) a)) =
      (S) ((η) (algebraMap (Ring K 1) (ChartRing (t)) a)) := by
  rw [completeIdentityFirstPoleTargetMap_algebraMap,
    completeIdentityFirstPoleSourceMap_algebraMap]
  apply congrArg (ι)
  dsimp only [completeIdentityFirstPoleTarget, completeIdentityFirstPoleSource,
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [ringMap_scalar, AlgHom.commutes]
  exact congrArg (ρ) (completeIdentityFirstNodePolynomialMap_coefficients K n h a).symm

/-- Their difference is exactly the original ambient error on the common patch. -/
theorem completeIdentityFirstPolePatch_error (z : ChartRing (t)) :
    (Q) ((η) z) - (S) ((η) z) =
      (ι) ((ρ) (completeIdentityFirstAmbientError K n h z)) := by
  rw [completeIdentityFirstPoleTargetMap_algebraMap,
    completeIdentityFirstPoleSourceMap_algebraMap]
  simp only [completeIdentityFirstPoleTarget, completeIdentityFirstPoleSource,
    completeIdentityFirstAmbientError, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, map_sub]

end FLT.Mazur.PolygonInfinitesimalStages

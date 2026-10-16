/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopPolePatchGeometry

/-!
# Original source poles without a target-denominator hypothesis

This is the literal localization of the original affine patch at its
scaled source marking denominator. The target and all original equations
remain unchanged; no target marking or parameter is inverted.
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

/-- Invert only the original scaled source denominator on the original affine patch. -/
abbrev CompleteIdentityTopSourcePolePatch := Localization.Away ((s) (d))
local notation "Z" => CompleteIdentityTopSourcePolePatch K n h m U
local notation "ι" => algebraMap Γ((R), (V).1) (Z)

/-- The original source poles require no target-denominator inversion. -/
def completeIdentityTopSourcePoleFunctions : StageNodeLocalization K (m + 1) →+* (Z) :=
  IsLocalization.Away.lift (d) (g := (ι).comp (s))
    (IsLocalization.Away.algebraMap_isUnit ((s) (d)))
local notation "S" => completeIdentityTopSourcePoleFunctions K n h m U
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K (m + 1))

/-- The source-only extension retains every original scaled numerator. -/
theorem completeIdentityTopSourcePoleFunctions_algebraMap (z : ChartRing (t)) :
    (S) ((η) z) = (ι) ((s) z) := IsLocalization.Away.lift_eq _ _ _

/-- The source-only localization maps to the full unchanged original affine patch. -/
def completeIdentityTopSourcePolePatchMap : Spec (.of (Z)) ⟶ (V).1.toScheme :=
  AffineOpenSpectrumFunctions.map (V) (CommRingCat.ofHom (ι))
local notation "M" => completeIdentityTopSourcePolePatchMap K n h m U
local notation "p" => (pullback.fst _ _ ≫ Iso.inv (stageNodeParameterIso K (m + 1)) :
  (R) ⟶ chart (Ring K[T;T⁻¹] (m + 1)) (e))

/-- The original source projection retains precisely its reciprocal substitution. -/
@[reassoc] theorem completeIdentityTopSourcePolePatchMap_source :
    (M) ≫ (V).1.ι ≫ (p) ≫ Spec.map (CommRingCat.ofHom ((σ).toRingHom.comp (b))) =
      Spec.map (CommRingCat.ofHom (S)) ≫ Spec.map (CommRingCat.ofHom (η)) := by
  rw [← Category.assoc (V).1.ι, ← Category.assoc (M),
    completeIdentityTopSourcePolePatchMap, AffineOpenSpectrumFunctions.map_comp_inclusion]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (completeIdentityTopSourcePoleFunctions_algebraMap K n h m U z).symm

end FLT.Mazur.PolygonInfinitesimalStages

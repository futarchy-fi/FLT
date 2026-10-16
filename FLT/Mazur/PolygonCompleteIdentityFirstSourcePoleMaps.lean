/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPolePatchGeometry

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

/-- Invert only the original scaled source denominator on the original affine patch. -/
abbrev CompleteIdentityFirstSourcePolePatch := Localization.Away ((s) (d))
local notation "Z" => CompleteIdentityFirstSourcePolePatch K n h U
local notation "ι" => algebraMap Γ((R), (V).1) (Z)

/-- The original source poles require no target-denominator inversion. -/
def completeIdentityFirstSourcePoleFunctions : StageNodeLocalization K 1 →+* (Z) :=
  IsLocalization.Away.lift (d) (g := (ι).comp (s))
    (IsLocalization.Away.algebraMap_isUnit ((s) (d)))
local notation "S" => completeIdentityFirstSourcePoleFunctions K n h U
local notation "η" => algebraMap (ChartRing (t)) (StageNodeLocalization K 1)

/-- The source-only extension retains every original scaled numerator. -/
theorem completeIdentityFirstSourcePoleFunctions_algebraMap (z : ChartRing (t)) :
    (S) ((η) z) = (ι) ((s) z) := IsLocalization.Away.lift_eq _ _ _

/-- The source-only localization maps to the full unchanged original affine patch. -/
def completeIdentityFirstSourcePolePatchMap : Spec (.of (Z)) ⟶ (V).1.toScheme :=
  AffineOpenSpectrumFunctions.map (V) (CommRingCat.ofHom (ι))
local notation "M" => completeIdentityFirstSourcePolePatchMap K n h U
local notation "p" => (pullback.fst _ _ ≫ Iso.inv (firstNodeParameterIso K) :
  (R) ⟶ chart (Ring K[T;T⁻¹] 1) (e))

/-- The original source projection retains precisely its reciprocal substitution. -/
@[reassoc] theorem completeIdentityFirstSourcePolePatchMap_source :
    (M) ≫ (V).1.ι ≫ (p) ≫ Spec.map (CommRingCat.ofHom ((σ).toRingHom.comp (b))) =
      Spec.map (CommRingCat.ofHom (S)) ≫ Spec.map (CommRingCat.ofHom (η)) := by
  rw [← Category.assoc (V).1.ι, ← Category.assoc (M),
    completeIdentityFirstSourcePolePatchMap, AffineOpenSpectrumFunctions.map_comp_inclusion]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (completeIdentityFirstSourcePoleFunctions_algebraMap K n h U z).symm

end FLT.Mazur.PolygonInfinitesimalStages

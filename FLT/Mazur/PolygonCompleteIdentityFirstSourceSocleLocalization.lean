/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeSocleLocalization
public import FLT.Mazur.PolygonCompleteIdentityFirstChartResidualCoordinates
public import FLT.Mazur.PolygonCompleteIdentityFirstChartFiberSocle
public import FLT.Mazur.PolygonSmoothingNodeBasicOpen

/-!
# The source pole localization retains the full original closed-fiber socle

The actual reciprocally scaled marking denominator acts identically on
every original source-coordinate common annihilator. Its localization is
therefore faithful on the remaining socle, including all graph nilpotents.
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
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "Q" => completeIdentityFirstChartClosedFiber K n h
local notation "q" => completeIdentityFirstChartClosedQuotient K n h
local notation "s" => completeIdentityFirstChartSourceFunctions K n h
local notation "f" => RingHom.comp (q) (s)
local notation "u" => parameterUnit K
local notation "σ" => reciprocalScale (e) (u)
local notation "b" => ringMap (stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1)
  (t) (e) (stageCoefficientMap_parameter _ _)
local notation "x" => (q) (completeIdentityFirstChartSourceX K n h)
local notation "y" => (q) (completeIdentityFirstChartSourceY K n h)
local notation "X" => (f) ((σ) ((b) (leftCoordinate (t))))
local notation "Y" => (f) ((σ) ((b) (rightCoordinate (t))))

/-- The original scaled source marking denominator in the full closed graph fiber. -/
def completeIdentityFirstClosedSourceDenominator : Q :=
  (f) ((σ) ((b) (nodeMarkingDenominator (t))))
local notation "D" => completeIdentityFirstClosedSourceDenominator K n h

/-- The same denominator retains the two actual scaled source coordinates. -/
theorem completeIdentityFirstClosedSourceDenominator_eq : (D) = (1 - (X)) * (1 - (Y)) := by
  let g := (f).comp ((σ).toRingHom.comp (b))
  change g (nodeMarkingDenominator (t)) =
    (1 - g (leftCoordinate (t))) * (1 - g (rightCoordinate (t)))
  rw [nodeMarkingDenominator, g.map_mul, g.map_sub, g.map_sub, g.map_one]

/-- Original source annihilators remain annihilators after the unchanged reciprocal scaling. -/
theorem completeIdentityFirstClosedScaledSource_socle (z : Q)
    (hx : (x) * z = 0) (hy : (y) * z = 0) : (X) * z = 0 ∧ (Y) * z = 0 := by
  constructor
  · rw [ringMap_left, reciprocalScale_left, (f).map_mul, mul_assoc]
    change _ * ((x) * z) = 0
    rw [hx, mul_zero]
  · rw [ringMap_right, reciprocalScale_right, (f).map_mul, mul_assoc]
    change _ * ((y) * z) = 0
    rw [hy, mul_zero]

/-- The source pole denominator is exactly the identity on the entire original node socle. -/
theorem completeIdentityFirstClosedSourceDenominator_socle (z : Q)
    (hx : (x) * z = 0) (hy : (y) * z = 0) : (D) * z = z := by
  obtain ⟨hl, hr⟩ := completeIdentityFirstClosedScaledSource_socle K n h z hx hy
  rw [completeIdentityFirstClosedSourceDenominator_eq]
  exact NodeSocleLocalization.denominator_mul (X) (Y) z hl hr

/-- Localizing at this actual source denominator loses no original closed-fiber socle element. -/
theorem completeIdentityFirstClosedSourceSocle_localization (z : Q)
    (hx : (x) * z = 0) (hy : (y) * z = 0)
    (hz : algebraMap (Q) (Localization.Away (D)) z = 0) : z = 0 := by
  obtain ⟨hl, hr⟩ := completeIdentityFirstClosedScaledSource_socle K n h z hx hy
  rw [completeIdentityFirstClosedSourceDenominator_eq] at hz
  exact NodeSocleLocalization.eq_zero_of_localization (X) (Y) z hl hr hz

/-- It suffices to eliminate the retained full source socle after the actual pole localization. -/
theorem completeIdentityFirstGraphToChart_isIso_of_sourcePoleSocle
    (hs : ∀ z : Q, (x) * z = 0 → (y) * z = 0 →
      algebraMap (Q) (Localization.Away (D)) z = 0) :
    IsIso (completeIdentityFirstGraphToChart K n h) := by
  apply completeIdentityFirstGraphToChart_isIso_of_closedSocle K n h
  intro z hx hy
  exact completeIdentityFirstClosedSourceSocle_localization K n h z hx hy (hs z hx hy)

end FLT.Mazur.PolygonInfinitesimalStages

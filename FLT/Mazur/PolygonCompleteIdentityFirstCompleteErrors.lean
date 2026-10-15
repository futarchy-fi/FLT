/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicAmbientLifts
public import FLT.Mazur.PolygonCompleteIdentityFirstChartAmbientErrors
public import FLT.Mazur.PolygonCompleteIdentityFirstChartLocalEquations

/-!
# Complete ambient representatives of the original first-stage errors

On each transported affine patch, lift the actual source and target functions
separately and subtract. The resulting complete functions specialize to the
original errors, rather than to functions in a branch-image quotient. Chosen
section lifts are not asserted to form a ring homomorphism.
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
local notation "t" => parameter K 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "B" => ChartRing (t)
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "a" => stageCoefficientMap (C : K →+* K[T;T⁻¹]) 1
local notation "b" => ringMap (a) (t) (e) (stageCoefficientMap_parameter _ _)
local notation "σ" => reciprocalScale (e) (parameterUnit K)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "W" => completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "p" => completeIdentityAdicAmbientPatchMap K n h 1 0 0 U
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "L" => completeIdentityAdicAmbientLift K n h 1 0 0 U

/-- A complete lift of the unchanged source function on this original ambient patch. -/
def completeIdentityFirstCompleteSource (z : ChartRing (e)) :
    Γ(completeIdentityActionLiftSpace K n h, (W).1) :=
  (L) (completeIdentityFirstAmbientSourceFunctions K n h z)

/-- A complete lift of the unchanged target function on the same ambient patch. -/
def completeIdentityFirstCompleteTarget (z : B) :
    Γ(completeIdentityActionLiftSpace K n h, (W).1) :=
  (L) (completeIdentityFirstAmbientTargetFunctions K n h z)

/-- A complete error representative, constructed from the actual target and scaled source. -/
def completeIdentityFirstCompleteError (z : B) :
    Γ(completeIdentityActionLiftSpace K n h, (W).1) :=
  completeIdentityFirstCompleteTarget K n h U z -
    completeIdentityFirstCompleteSource K n h U ((σ) ((b) z))

/-- The complete source representative retains the original source function. -/
theorem completeIdentityFirstCompleteSource_spec (z : ChartRing (e)) :
    (p) (completeIdentityFirstCompleteSource K n h U z) =
      (ρ) (completeIdentityFirstAmbientSourceFunctions K n h z) :=
  completeIdentityAdicAmbientLift_spec K n h 1 0 0 U _

/-- The complete target representative retains the original target function. -/
theorem completeIdentityFirstCompleteTarget_spec (z : B) :
    (p) (completeIdentityFirstCompleteTarget K n h U z) =
      (ρ) (completeIdentityFirstAmbientTargetFunctions K n h z) :=
  completeIdentityAdicAmbientLift_spec K n h 1 0 0 U _

/-- The complete error specializes to the actual full original ambient error. -/
theorem completeIdentityFirstCompleteError_spec (z : B) :
    (p) (completeIdentityFirstCompleteError K n h U z) =
      (ρ) (completeIdentityFirstAmbientError K n h z) := by
  rw [completeIdentityFirstCompleteError, map_sub,
    completeIdentityFirstCompleteTarget_spec, completeIdentityFirstCompleteSource_spec,
    completeIdentityFirstAmbientError, map_sub]

/-- Both actual coordinate errors lift on a common complete affine neighborhood of each point. -/
theorem completeIdentityFirstCompleteErrors_cover (x : R) :
    ∃ U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens,
      x ∈ (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U).1 ∧
      ∀ z : B, completeIdentityAdicAmbientPatchMap K n h 1 0 0 U
        (completeIdentityFirstCompleteError K n h U z) =
        (R).presheaf.map (homOfLE (show
          (completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U).1 ≤ ⊤ from le_top)).op
          (completeIdentityFirstAmbientError K n h z) := by
  obtain ⟨U, hx⟩ := completeIdentityAdicAmbientPatch_cover K n h 1 0 0 x
  exact ⟨U, hx, completeIdentityFirstCompleteError_spec K n h U⟩

end FLT.Mazur.PolygonInfinitesimalStages

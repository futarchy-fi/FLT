/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPoleSourceGeometry

/-!
# The unchanged universal input functions on the original pole patch

Keep the independent Laurent coordinate before reciprocal substitution.
The parameter in this ring is precisely the original ambient parameter.
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
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
local notation "t" => parameter K 1
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "Z" => CompleteIdentityFirstPolePatch K n h U
local notation "M" => completeIdentityFirstPolePatchMap K n h U
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "ι" => algebraMap Γ((R), (V).1) (Z)

/-- The original ambient smoothing parameter on the unchanged common pole patch. -/
abbrev completeIdentityFirstPoleParameter : (Z) :=
  (ι) ((ρ) (completeIdentityFirstAmbientParameter K n h))

/-- The original universal source functions on the same unchanged common pole patch. -/
def completeIdentityFirstPoleInputFunctions : ChartRing (C (t)) →+* (Z) :=
  (ι).comp ((ρ).hom.comp ((completeIdentityFirstAmbientSourceFunctions K n h).comp
    (firstNodeParameterMap K)))
local notation "F" => completeIdentityFirstPoleInputFunctions K n h U

/-- These functions are exactly the actual original source projection in universal coordinates. -/
@[reassoc] theorem completeIdentityFirstPoleInputFunctions_map :
    Spec.map (CommRingCat.ofHom (F)) = (M) ≫ (V).1.ι ≫ pullback.fst _ _ := by
  have he := AffineOpenSpectrumFunctions.map_comp_inclusion (V) (CommRingCat.ofHom (ι))
    (pullback.fst _ _ ≫ (firstNodeParameterIso K).inv)
  have hh := congrArg (fun z ↦ z ≫ (firstNodeParameterIso K).hom) he
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hh
  rw [firstNodeParameterIso_hom, ← Spec.map_comp] at hh
  exact hh.symm

/-- Its smoothing parameter is the original ambient parameter restricted and localized. -/
theorem completeIdentityFirstPoleInputFunctions_parameter :
    (F) (algebraMap (Ring K 1)[T;T⁻¹] (ChartRing (C (t))) (C (t))) =
      (ι) ((ρ) (completeIdentityFirstAmbientParameter K n h)) := by
  dsimp only [completeIdentityFirstPoleInputFunctions, RingHom.comp_apply]
  rw [firstNodeParameterMap, ringMap_scalar, parameterEval_parameter]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginNeighborhood
public import FLT.Mazur.PolygonCompletePointIdentityEquation

/-!
# The actual parameter neighborhood inside the original Y chart

The original parameter preimage lies inside the original Y generator open.
Its map to the localized cubic chart agrees with the original Y-chart map,
with both actual inclusions retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve FCurve.ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  divisorLineBundle ModuleSheafTensor.tensor

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "s" => completeBaseMarking K n h i
local notation "hI" => And.left (completeBaseMarking_relativeCartier K n h i)
local notation "L" => divisorLineBundle (Scheme.Hom.ker (s)) hI
local notation "T" => completePointProjectiveSections K n h i
local notation "U" => sectionGeneratorOpen (tensorPower (L) 3) (T 1)
local notation "V" => completePointOriginOpen K n h i
local notation "g" => completePointToIntegralCubic K n h i

/-- The actual parameter preimage is contained in the original Y generator open. -/
theorem completePointOriginOpen_le_y : (V) ≤ (U) := by
  rw [← completePointToIntegralCubic_preimage_chart K n h i 1]
  intro x hx
  change (g) x ∈ Set.range (integralCurveChart (W) 1)
  change (g) x ∈ Set.range (originNeighborhoodInclusion (W)) at hx
  obtain ⟨z, hz⟩ := hx
  exact ⟨PrincipalAffineRefinement.inclusion (originDenominator (W)) z, hz⟩

/-- The genuine inclusion of the parameter preimage into the original Y open. -/
def completePointOriginToY : (V).toScheme ⟶ (U).toScheme :=
  (exactVeroneseProj K n h).homOfLE (completePointOriginOpen_le_y K n h i)

/-- The inclusion retains the original open immersion into the complete family. -/
@[reassoc] theorem completePointOriginToY_inclusion :
    completePointOriginToY K n h i ≫ (U).ι = (V).ι :=
  Scheme.homOfLE_ι _ _

/-- The parameter map restricts the original cubic Y-chart map. -/
@[reassoc] theorem completePointToOrigin_chart :
    completePointToOrigin K n h i ≫
      PrincipalAffineRefinement.inclusion (originDenominator (W)) =
        completePointOriginToY K n h i ≫ completePointToCubicChart K n h i 1 := by
  apply (cancel_mono (integralCurveChart (W) 1)).mp
  rw [Category.assoc, Category.assoc, completePointToCubicChart_inclusion,
    completePointOriginToY_inclusion_assoc]
  exact completePointToOrigin_inclusion K n h i

end FLT.Mazur.PolygonInfinitesimalStages

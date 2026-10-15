/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ImmersionAffineLifts
public import FLT.Mazur.PolygonCompleteIdentityAdicAmbientImmersion

/-!
# Original adic functions lifted to affine opens of the complete lifting space

The transported patches lie in the original complete lifting space, and their
full inverse images in the actual adic chart are affine. Every global adic
function has a local complete lift on each patch, without imposing a graph
ideal or replacing the original ambient relation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i j : Fin n)
local notation "R" => completeIdentityActionAdicChartSpace K n h m i j
local notation "k" => completeIdentityActionAdicChartSpaceMap K n h m i j ≫
  completeIdentityActionAdicLiftSpaceMap K n h m
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h m i j).toScheme.affineOpens)

/-- An affine patch of the original complete lifting space. -/
abbrev completeIdentityAdicAmbientTargetPatch := ImmersionAffineLifts.target (k) U

/-- The full affine inverse image of this patch in the actual original adic relation. -/
abbrev completeIdentityAdicAmbientSourcePatch := ImmersionAffineLifts.source (k) U
local notation "W" => completeIdentityAdicAmbientTargetPatch K n h m i j U
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h m i j U

/-- The source patch is exactly the inverse image under the original ambient map. -/
theorem completeIdentityAdicAmbientPatch_preimage : (V).1 = (k) ⁻¹ᵁ (W).1 :=
  ImmersionAffineLifts.source_eq (k) U

/-- The actual restriction of complete ambient functions to the original adic patch. -/
abbrev completeIdentityAdicAmbientPatchMap :
    Γ(completeIdentityActionLiftSpace K n h, (W).1) ⟶ Γ((R), (V).1) :=
  (k).appLE (W) (V) (le_of_eq (completeIdentityAdicAmbientPatch_preimage K n h m i j U))
local notation "p" => completeIdentityAdicAmbientPatchMap K n h m i j U

/-- Every local original adic function has a complete ambient lift on this very patch. -/
theorem completeIdentityAdicAmbientPatchMap_surjective : Function.Surjective (p) :=
  ImmersionAffineLifts.sections_surjective (k) U

/-- A chosen complete ambient lift of an original global adic function. -/
def completeIdentityAdicAmbientLift (z : Γ((R), ⊤)) :
    Γ(completeIdentityActionLiftSpace K n h, (W).1) :=
  (completeIdentityAdicAmbientPatchMap_surjective K n h m i j U
    ((R).presheaf.map (homOfLE (show (V).1 ≤ ⊤ from le_top)).op z)).choose

/-- The lift restricts to the original global function, including all nilpotents. -/
theorem completeIdentityAdicAmbientLift_spec (z : Γ((R), ⊤)) :
    (p) (completeIdentityAdicAmbientLift K n h m i j U z) =
      (R).presheaf.map (homOfLE (show (V).1 ≤ ⊤ from le_top)).op z :=
  (completeIdentityAdicAmbientPatchMap_surjective K n h m i j U _).choose_spec

/-- The transported affine patches cover every original ambient point. -/
theorem completeIdentityAdicAmbientPatch_cover (x : R) :
    ∃ U : (completeIdentityActionAdicChartAmbientOpen K n h m i j).toScheme.affineOpens,
      x ∈ (completeIdentityAdicAmbientSourcePatch K n h m i j U).1 :=
  ImmersionAffineLifts.exists_patch (k) x

end FLT.Mazur.PolygonInfinitesimalStages

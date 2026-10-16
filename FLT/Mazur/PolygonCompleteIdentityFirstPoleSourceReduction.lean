/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstPoleInputFunctions
public import FLT.Mazur.PolygonCompleteIdentityFirstPoleTargetCubic
public import FLT.Mazur.PolygonCompleteIdentityFirstSourceZeroCubic

/-!
# Source and target cubic maps agree after killing the actual parameter

The comparison uses the original order-zero action law and the constructed
full source factorization. It applies to every receiving ring, including
nonreduced quotients, without passing to a branch image or radical ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h 1 0 0).toScheme.affineOpens)
variable (hC : (completeIdentityAdicAmbientTargetPatch K n h 1 0 0 U).1 ≤
  completeIdentityCubicChartOpen K n h 2)
local notation "V" => completeIdentityAdicAmbientSourcePatch K n h 1 0 0 U
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "Z" => CompleteIdentityFirstPolePatch K n h U
local notation "ρ" => completeIdentityFirstAmbientRestriction K n h (V)
local notation "ι" => algebraMap Γ((R), (V).1) (Z)
local notation "τ" => (ι) ((ρ) (completeIdentityFirstAmbientParameter K n h))
local notation "Q" => completeIdentityFirstPoleTargetMap K n h U
local notation "S" => completeIdentityFirstPoleSourceMap K n h U
local notation "F" => completeIdentityFirstPoleInputFunctions K n h U
local notation "M" => completeIdentityFirstPolePatchMap K n h U
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "c" => completeIdentityAdicCubicChartMap K n h 1 0 0 U 2 hC
local notation "d" => completePointNodeToCubicChart K n h 1 0 0
variable {B : Type} [CommRing B]
variable (φ : CompleteIdentityFirstPolePatch K n h U →+* B)
variable (hf : φ (completeIdentityFirstPoleParameter K n h U) = 0)

include hC hf

/-- The reciprocal source and actual complete action agree in every parameter quotient. -/
theorem completeIdentityFirstPoleSource_cubic_of_parameter_zero :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (S)) ≫ (d) =
      Spec.map (CommRingCat.ofHom φ) ≫ (M) ≫ (c) := by
  apply (cancel_mono (integralCurveChart (E) 2)).mp
  simp only [Category.assoc, completeIdentityFirstPoleSource_universalScaling,
    completeIdentityAdicCubicChartMap_action, completeIdentityActionAdicLiftSpaceMap,
    pullback.lift_fst_assoc, completeIdentityActionAdicChartSpaceMap_fst_assoc]
  rw [← completeIdentityFirstPoleInputFunctions_map_assoc,
    ← completeIdentityFirstPoleInputFunctions_map_assoc]
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  apply completeIdentityFirstSource_cubic_of_parameter_zero K n h 0 (φ.comp (F))
  change φ ((F) _) = 0
  rw [completeIdentityFirstPoleInputFunctions_parameter]
  exact hf

/-- Both unchanged node cubic charts therefore have the same values in every such quotient. -/
theorem completeIdentityFirstPoleCharts_eq_of_parameter_zero :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (S)) ≫ (d) =
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (Q)) ≫ (d) := by
  rw [completeIdentityFirstPoleTarget_cubicChart K n h U hC]
  exact completeIdentityFirstPoleSource_cubic_of_parameter_zero K n h U hC φ hf

/-- Every original cubic function has equal source and target images after parameter reduction. -/
theorem completeIdentityFirstPoleFunctions_eq_of_parameter_zero (z : Coordinate (E) 2) :
    φ ((S) (completePointNodeCubicFunctions K n h 1 0 0 z)) =
      φ ((Q) (completePointNodeCubicFunctions K n h 1 0 0 z)) := by
  have he := congrArg (fun v ↦ (Scheme.ΓSpecIso (.of (Coordinate (E) 2))).inv ≫
    v.appTop ≫ (Scheme.ΓSpecIso (.of B)).hom)
    (completeIdentityFirstPoleCharts_eq_of_parameter_zero K n h U hC φ hf)
  simp only [Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.ΓSpecIso_naturality_assoc] at he
  exact congrArg (fun v : CommRingCat.of (Coordinate (E) 2) ⟶ CommRingCat.of B ↦ v z) he

end FLT.Mazur.PolygonInfinitesimalStages

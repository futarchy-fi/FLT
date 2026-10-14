/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionGraph
public import FLT.Mazur.PolygonCompleteIdentityActionSectionProj

/-!
# Original base, full ideals, and full marking-section Proj on the graph closure

The proper correspondence preserves the unchanged contraction square with its
scheme structure. These identities do not identify its source with the original
input product; the projection still needs an inverse at node inputs.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve WeierstrassIntegralChart SectionGradedSum SectionGradedProjConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "l" => completeIdentityActionGraphLift K n h
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
local notation "π" => exactVeroneseProjToBase K n h
local notation "s" => completeIdentityActionSecond K n h

/-- The graph correspondence uses the literal original power-series base map. -/
@[reassoc] theorem completeIdentityActionGraphLift_structure :
    (l) ≫ (π) = (p) ≫ (s) ≫ (π) := by
  apply (cancel_mono (Scheme.toSpecΓ (Spec (.of (PowerSeries K))))).mp
  simp only [Category.assoc]
  rw [← completePointToIntegralCubic_over, completeIdentityActionGraphLift_contraction_assoc,
    completeIdentityActionTarget_structure, completePointToIntegralCubic_over]

/-- Every original cubic ideal has the same full pullback along both graph paths. -/
theorem completeIdentityActionGraphLift_ideal
    (I : (integralCurve (completePointWeierstrassCurve K n h 0)).IdealSheafData) :
    (I.comap (g)).comap (l) = (I.comap (a)).comap (p) := by
  rw [← Scheme.IdealSheafData.comap_comp, completeIdentityActionGraphLift_contraction,
    Scheme.IdealSheafData.comap_comp]

local notation "L" => completePointLine K n h (0 : Fin n)
local instance completeIdentityGraphCompatibilityLine : Fact (LocallyFreeRankOne (L)) :=
  ⟨completePointLine_locallyFreeRankOne K n h 0⟩

/-- The entire graph retains the canonical full marking-section-Proj square. -/
@[reassoc] theorem completeIdentityActionGraphLift_sectionProj :
    (l) ≫ toProj (L) (completePointLine_positivePowerGenerated K n h 0) =
      (p) ≫ completeIdentityActionSectionProjTarget K n h 0 := by
  apply (cancel_mono (completePointCanonicalCubicIso K n h 0).hom).mp
  simp only [Category.assoc, completePointCanonicalCubicIso_contraction,
    completeIdentityActionSectionProjTarget_cubic, completeIdentityActionGraphLift_contraction]

end FLT.Mazur.PolygonInfinitesimalStages

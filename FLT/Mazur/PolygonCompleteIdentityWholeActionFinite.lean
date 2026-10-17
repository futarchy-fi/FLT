/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityWholeAction
public import FLT.Mazur.PolygonCompleteIdentityFiniteGraphLift

/-!
# The whole action retains all original finite actions and cubic ideals

The global action identifies the entire original graph. Pulling its equality
back along the already constructed finite graph lifts recovers the original
finite actions exactly, including every nilpotent and singular input.
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
local notation "P" => completeIdentityActionProduct K n h 0
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "l" => completeIdentityActionGraphLift K n h
local notation "a" => completeIdentityWholeAction K n h
local notation "c" => completePointToIntegralCubic K n h 0

/-- The entire original graph has exactly the newly constructed global action as target. -/
@[reassoc] theorem completeIdentityWholeAction_graph : (p) ≫ (a) = (l) := by
  have he := completeIdentityActionFlatTestLift_graph K n h (𝟙 (P)) (a)
    (by simpa only [Category.id_comp] using completeIdentityWholeAction_cubic K n h)
  apply (cancel_epi (pullback.fst (p) (𝟙 (P)))).mp
  rw [← Category.assoc, pullback.condition, Category.comp_id, he]

/-- The full original graph projection is invertible, without discarding any components. -/
instance completeIdentityWholeAction_graph_isIso : IsIso (p) := by
  let _ := completeIdentityActionFlatTestLift_graph_isIso K n h (𝟙 (P)) (a)
    (by simpa only [Category.id_comp] using completeIdentityWholeAction_cubic K n h)
  have he : (p) = inv (pullback.fst (p) (𝟙 (P))) ≫ pullback.snd (p) (𝟙 (P)) := by
    apply (cancel_epi (pullback.fst (p) (𝟙 (P)))).mp
    rw [IsIso.hom_inv_id_assoc, pullback.condition, Category.comp_id]
  rw [he]
  infer_instance

/-- The global action recovers the original finite scaling at every order exactly. -/
@[reassoc] theorem completeIdentityWholeAction_finite (m : ℕ) :
    completeIdentityFiniteInput K n h 0 m ≫ (a) = completeIdentityFiniteScaling K n h m := by
  rw [← completeIdentityFiniteToGraph_source K n h m, Category.assoc,
    completeIdentityWholeAction_graph, completeIdentityFiniteToGraph_target]

/-- Every original cubic ideal retains its full scheme-theoretic pullback under the action. -/
theorem completeIdentityWholeAction_ideal
    (I : (integralCurve (completePointWeierstrassCurve K n h 0)).IdealSheafData) :
    (I.comap (c)).comap (a) = I.comap (completeIdentityActionTarget K n h 0) := by
  rw [← Scheme.IdealSheafData.comap_comp, completeIdentityWholeAction_cubic]

local notation "L" => completePointLine K n h (0 : Fin n)
local instance completeIdentityWholeActionLine : Fact (LocallyFreeRankOne (L)) :=
  ⟨completePointLine_locallyFreeRankOne K n h 0⟩

/-- The whole action retains the canonical Proj map of the original full marking section ring. -/
@[reassoc] theorem completeIdentityWholeAction_sectionProj :
    (a) ≫ toProj (L) (completePointLine_positivePowerGenerated K n h 0) =
      completeIdentityActionSectionProjTarget K n h 0 := by
  apply (cancel_mono (completePointCanonicalCubicIso K n h 0).hom).mp
  simp only [Category.assoc, completePointCanonicalCubicIso_contraction,
    completeIdentityActionSectionProjTarget_cubic, completeIdentityWholeAction_cubic]

end FLT.Mazur.PolygonInfinitesimalStages

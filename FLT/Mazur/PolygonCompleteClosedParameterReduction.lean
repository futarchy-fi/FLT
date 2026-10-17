/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedChartComparison
public import FLT.Mazur.PolygonCompleteFiniteParameterProduct

/-!
# Closed Laurent parameters retain their original finite-stage inclusions

The closed parameter chart factors through every original finite Laurent
parameter, with its actual coefficient reduction and its original cyclic label.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj completeClosedFiberInclusion
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual closed coefficient map on the whole Laurent parameter scheme. -/
def completeClosedParameterReduction (m : ℕ) :
    Spec (.of (LaurentPolynomial K)) ⟶ (completeFiniteParameterOver K m).left :=
  Spec.map (CommRingCat.ofHom (PolygonScalingNaturality.coeffMap (reduction K m).toRingHom))

/-- Every finite identity torus restricts to the unchanged original closed torus. -/
@[reassoc] theorem completeClosedParameterReduction_identity (i : Fin n) (m : ℕ) :
    completeClosedParameterReduction K m ≫ completeIdentityStageTorus K n h i m =
      completePointIdentityClosedTorus K n h i := by
  apply (cancel_mono (completePointIdentityOpen K n h i).ι).mp
  rw [Category.assoc, completeIdentityStageTorus_inclusion,
    completePointIdentityClosedTorus_inclusion]
  rw [← Category.assoc]
  unfold completeClosedParameterReduction
  change (_ ≫ PolygonInfinitesimal.edge _ _ n h i) ≫ _ = _
  rw [(originalTorus_stageEdge_isPullback K n h i m).w, Category.assoc,
    specialFiberInclusion_toComplete]

/-- The finite rotated parameter restricts to exactly the original closed smooth chart. -/
@[reassoc] theorem completeClosedParameterReduction_parameter (i : Fin n) (m : ℕ) :
    completeClosedParameterReduction K m ≫
        (completeFiniteParameter K n h m (ZMod.finEquiv n i)).left =
      completeClosedFiniteChart K n h i ≫ completeClosedSmoothInclusion K n h := by
  rw [completeClosedFiniteChart_zeroIdentityChart]
  change _ ≫ (completeIdentityStageTorus K n h 0 m ≫ _) = _
  rw [← Category.assoc, completeClosedParameterReduction_identity]

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChartSpace

/-!
# Original adic node-relation functions lift locally to the complete ambient space

The whole adic lifting space is closed in the original complete lifting
space. Its two-node chart is therefore locally closed. Factoring this
immersion gives actual surjective affine section maps before imposing the
graph equations, so local stage functions have complete ambient lifts.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
attribute [local instance] originalStageToCompatibleProj_isClosedImmersion
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "f" => completeIdentityFiniteInput K n h 0 m
local notation "r" => originalStageToCompatibleProj K n h m
local notation "a" => completeIdentityActionTarget K n h 0
local notation "g" => completePointToIntegralCubic K n h 0

/-- Both original adic coordinates cut out a closed subscheme of the complete lifting space. -/
instance completeIdentityActionAdicLiftSpaceMap_closed :
    IsClosedImmersion (completeIdentityActionAdicLiftSpaceMap K n h m) := by
  change IsClosedImmersion
    (pullback.map ((f) ≫ (a)) ((r) ≫ (g)) (a) (g) (f) (r) (𝟙 _) (by simp) (by simp))
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    inferInstance inferInstance rfl rfl

variable (i j : Fin n)
local notation "R" => completeIdentityActionAdicChartSpace K n h m i j
local notation "k" => completeIdentityActionAdicChartSpaceMap K n h m i j ≫
  completeIdentityActionAdicLiftSpaceMap K n h m

/-- The full original two-node relation is locally closed in the complete lifting space. -/
instance completeIdentityActionAdicChartSpace_immersion : IsImmersion (k) := inferInstance

/-- An actual open of the complete ambient space in which the stage chart is closed. -/
abbrev completeIdentityActionAdicChartAmbientOpen := (k).coborderRange

/-- The full original stage chart has a closed immersion into this complete ambient open. -/
def completeIdentityActionAdicChartAmbientClosed :
    (R) ⟶ (completeIdentityActionAdicChartAmbientOpen K n h m i j).toScheme :=
  (k).liftCoborder

instance completeIdentityActionAdicChartAmbientClosed_closed :
    IsClosedImmersion (completeIdentityActionAdicChartAmbientClosed K n h m i j) := by
  unfold completeIdentityActionAdicChartAmbientClosed
  infer_instance

/-- The factorization retains the exact original map, before any graph ideal is imposed. -/
@[reassoc] theorem completeIdentityActionAdicChartAmbientClosed_inclusion :
    completeIdentityActionAdicChartAmbientClosed K n h m i j ≫
      (completeIdentityActionAdicChartAmbientOpen K n h m i j).ι = (k) :=
  Scheme.Hom.liftCoborder_ι _

/-- Every local original stage function lifts to a complete ambient function on this affine open. -/
theorem completeIdentityActionAdicChartAmbientClosed_sections
    (U : (completeIdentityActionAdicChartAmbientOpen K n h m i j).toScheme.affineOpens) :
    Function.Surjective ((completeIdentityActionAdicChartAmbientClosed K n h m i j).app U) :=
  (completeIdentityActionAdicChartAmbientClosed K n h m i j).app_surjective U.1 U.2

end FLT.Mazur.PolygonInfinitesimalStages

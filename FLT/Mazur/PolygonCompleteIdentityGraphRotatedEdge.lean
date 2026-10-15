/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentitySmoothInputGraph
public import FLT.Mazur.PolygonCompleteIdentityFiniteCoordinates
public import FLT.Mazur.PolygonCompleteIdentityFiniteRotatedEdges

/-!
# Every original finite edge in the complete cubic graph

The original finite pair and its actual rotated second chart construct a
point of the graph closure. The target is original multiplication followed
by the same rotation, including on the adjacent incoming component.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonSmoothing PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (b : ZMod n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "j" => edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (rotateIndex b 0)

/-- The actual full rotated edge maps to the complete graph with its original defining ideal. -/
def completeIdentityRotatedEdgeToGraph :
    branchTorus (A)[T;T⁻¹] ⟶ completeIdentityActionGraphClosure K n h :=
  completeIdentityFinitePair K n h 0 m ≫
    (𝟙 (G).X ⊗ₘ completeIdentityChart K n h 0 b).left ≫
      completeIdentitySmoothInputToGraph K n h

/-- The constructed graph point retains the original finite input on the labeled edge. -/
@[reassoc] theorem completeIdentityRotatedEdgeToGraph_source :
    completeIdentityRotatedEdgeToGraph K n h m b ≫
      completeIdentityActionGraphProjection K n h =
        (j) ≫ completeIdentityFiniteInput K n h 0 m := by
  rw [completeIdentityRotatedEdgeToGraph, Category.assoc, Category.assoc,
    completeIdentitySmoothInputToGraph_source]
  exact completeIdentityFinitePair_rotatedInput K n h m b

/-- Its target is the original group product on the original rotated component. -/
@[reassoc] theorem completeIdentityRotatedEdgeToGraph_target :
    completeIdentityRotatedEdgeToGraph K n h m b ≫ completeIdentityActionGraphLift K n h =
      completeIdentityFiniteOriginalMul K n h 0 m ≫
        (completePointIdentityOpen K n h 0).ι ≫ completeRotation K n h b := by
  rw [completeIdentityRotatedEdgeToGraph, Category.assoc, Category.assoc,
    completeIdentitySmoothInputToGraph_rotated]
  rfl

/-- The target is exactly the rotated original finite Laurent multiplication coordinate. -/
@[reassoc] theorem completeIdentityRotatedEdgeToGraph_coordinates :
    completeIdentityRotatedEdgeToGraph K n h m b ≫ completeIdentityActionGraphLift K n h =
      completeIdentityFiniteMulCoordinates K n h 0 m ≫
        edge (A) (t) n h (rotateIndex b 0) ≫ originalStageToCompatibleProj K n h m := by
  rw [completeIdentityRotatedEdgeToGraph_target,
    ← completeIdentityFiniteMulCoordinates_original, Category.assoc,
    completeIdentityStageEdge_rotation]

end FLT.Mazur.PolygonInfinitesimalStages

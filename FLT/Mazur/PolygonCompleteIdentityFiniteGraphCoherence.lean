/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFiniteGraphLift
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicClosed
public import FLT.Mazur.PolygonCompleteIdentityFiniteCoherence

/-!
# Compatible closed finite graphs inside the original complete graph

The entire original finite action inputs embed as closed subschemes of the
unchanged complete graph. Their maps agree under the original adjacent
restriction, retaining both source and target coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "l" => completeIdentityActionGraphLift K n h
local notation "j" => completeIdentityActionGraphInclusion K n h

/-- Both original coordinates uniquely determine a map into the full graph closure. -/
theorem completeIdentityGraph_coordinates_ext {T : Scheme}
    (f g : T ⟶ completeIdentityActionGraphClosure K n h)
    (hs : f ≫ (p) = g ≫ (p)) (ht : f ≫ (l) = g ≫ (l)) : f = g := by
  apply (cancel_mono (j)).mp
  apply pullback.hom_ext
  · exact hs
  · exact ht

/-- Each original whole finite input is closed in the actual complete graph. -/
instance completeIdentityFiniteToGraph_closed (m : ℕ) :
    IsClosedImmersion (completeIdentityFiniteToGraph K n h m) := by
  have : IsClosedImmersion (completeIdentityFiniteToGraph K n h m ≫ (p)) := by
    rw [completeIdentityFiniteToGraph_source]
    infer_instance
  exact IsClosedImmersion.of_comp _ (p)

/-- The constructed graph maps agree on the full adjacent original thickening. -/
@[reassoc] theorem completeIdentityFiniteToGraph_restriction (m : ℕ) :
    completeIdentityFiniteRestriction K n h m ≫ completeIdentityFiniteToGraph K n h (m + 1) =
      completeIdentityFiniteToGraph K n h m := by
  apply completeIdentityGraph_coordinates_ext K n h
  · rw [Category.assoc, completeIdentityFiniteToGraph_source,
      completeIdentityFiniteToGraph_source, completeIdentityFiniteRestriction_input]
  · rw [Category.assoc, completeIdentityFiniteToGraph_target,
      completeIdentityFiniteToGraph_target, completeIdentityFiniteRestriction_scaling]

/-- Every original rotated-edge factorization is retained by the whole-input construction. -/
@[reassoc] theorem completeIdentityFiniteToGraph_edge (m : ℕ) (b : ZMod n) :
    PolygonInfinitesimal.edge (LaurentPolynomial (Ring K m))
        (LaurentPolynomial.C (parameter K m)) n h (PolygonPinching.rotateIndex b 0) ≫
      completeIdentityFiniteToGraph K n h m = completeIdentityRotatedEdgeToGraph K n h m b := by
  apply (cancel_mono (j)).mp
  rw [Category.assoc, completeIdentityFiniteToGraph_inclusion,
    completeIdentityFiniteGraphMap_edge]

end FLT.Mazur.PolygonInfinitesimalStages

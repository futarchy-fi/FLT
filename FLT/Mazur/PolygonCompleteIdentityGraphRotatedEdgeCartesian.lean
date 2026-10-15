/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphEdgeCartesian
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicRotatedEdge

/-!
# Full preimages of the original rotated edges

Every rotated original finite edge is the entire complete and adic graph
preimage of its source. This includes the adjacent incoming component.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonPinching MonoidalCategory
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
variable (m : ℕ) (b : ZMod n)
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "j" => edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (rotateIndex b 0)
local notation "f" => completeIdentityFiniteInput K n h (0 : Fin n) m
local notation "o" => completeIdentityActionInputStageOriginalIso K n h m
local notation "v" => completeIdentityRotatedEdgeToAdicGraph K n h m b
local notation "q" => completeIdentityActionGraphStageProjection K n h m

/-- No extra complete-graph points or nilpotents occur over the original finite rotated edge. -/
theorem completeIdentityRotatedEdgeToGraph_isPullback :
    IsPullback (completeIdentityRotatedEdgeToGraph K n h m b) (𝟙 _) (p) ((j) ≫ (f)) := by
  have H := completeIdentityActionSmoothFamily_isPullback K n h
    (completeIdentityFinitePair K n h 0 m ≫
      (𝟙 (G).X ⊗ₘ completeIdentityChart K n h 0 b).left ≫
        completeIdentitySmoothInputToOpen K n h)
  have hi := completeIdentityFinitePair_rotatedInput K n h m b
  change completeIdentityFinitePair K n h 0 m ≫
    (𝟙 (G).X ⊗ₘ completeIdentityChart K n h 0 b).left ≫
      completeIdentitySmoothActionInput K n h = (j) ≫ (f) at hi
  simpa only [completeIdentityRotatedEdgeToGraph, completeIdentitySmoothInputToGraph,
    Category.assoc, completeIdentitySmoothInputToOpen_input,
    hi] using H

/-- The literal adic graph has exactly the same full preimage over that finite edge. -/
theorem completeIdentityRotatedEdgeToAdicGraph_isPullback :
    IsPullback (v) (𝟙 _) (q) ((j) ≫ (o).hom) := by
  have H : IsPullback ((v) ≫ completeIdentityActionGraphStageInclusion K n h m) (𝟙 _)
      (p) (((j) ≫ (o).hom) ≫ completeIdentityActionInputStageInclusion K n h m) := by
    rw [completeIdentityRotatedEdgeToAdicGraph_complete, Category.assoc,
      completeIdentityActionInputStageOriginalIso_inclusion]
    exact completeIdentityRotatedEdgeToGraph_isPullback K n h m b
  apply H.of_right _ (IsPullback.of_hasPullback (p) _)
  simp only [completeIdentityRotatedEdgeToAdicGraph, pullback.lift_snd, Category.id_comp]

/-- The actual finite edge is an open subscheme of the whole literal adic graph. -/
instance completeIdentityRotatedEdgeToAdicGraph_open : IsOpenImmersion (v) :=
  MorphismProperty.of_isPullback
    (completeIdentityRotatedEdgeToAdicGraph_isPullback K n h m b).flip inferInstance

/-- Every adic-graph family over this original edge is its specified original edge lift. -/
theorem completeIdentityRotatedEdgeToAdicGraph_unique {T : Scheme}
    (g : T ⟶ completeIdentityActionGraphStage K n h m)
    (a : T ⟶ PolygonSmoothing.branchTorus (A)[T;T⁻¹])
    (he : g ≫ (q) = a ≫ (j) ≫ (o).hom) : g = a ≫ (v) := by
  have H := completeIdentityRotatedEdgeToAdicGraph_isPullback K n h m b
  have hs := H.lift_snd g a he
  rw [Category.comp_id] at hs
  rw [← hs]
  exact (H.lift_fst g a he).symm

end FLT.Mazur.PolygonInfinitesimalStages

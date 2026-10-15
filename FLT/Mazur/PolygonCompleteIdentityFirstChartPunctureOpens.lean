/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartPunctures
public import FLT.Mazur.CartesianFiniteFibers

/-!
# The original first chart's punctures are its source coordinate principal opens

Use the exact parameter isomorphism to read the two original source
coordinates as global functions on the literal graph chart. Their principal
opens are precisely the two original branch maps used in its finite image.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentFirstStageParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "S" => Ring K[T;T⁻¹] 1
local notation "e" => parameter K[T;T⁻¹] 1
local notation "H" => completeIdentityActionGraphAdicChart K n h 1 0 0
local notation "o" => firstNodeParameterIso K
local notation "l" => completeIdentityFirstLeftToGraphChart K n h
local notation "r" => completeIdentityFirstRightToGraphChart K n h

/-- The literal chart's unchanged source, expressed through the original parameter isomorphism. -/
def completeIdentityFirstChartSource : (H) ⟶ chart (S) (e) :=
  completeIdentityActionGraphAdicChartSource K n h 1 0 0 ≫ (o).inv
local notation "s" => completeIdentityFirstChartSource K n h

/-- The exact outgoing square in the retained parameter coordinates. -/
theorem completeIdentityFirstChartSource_left_isPullback :
    IsPullback (l) (𝟙 _) (s) (leftBranchOpen (S) (e)) := by
  apply (completeIdentityFirstLeftToGraphChart_isPullback K n h).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (o).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id]
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]

/-- The exact incoming square in the same retained parameter coordinates. -/
theorem completeIdentityFirstChartSource_right_isPullback :
    IsPullback (r) (𝟙 _) (s) (rightBranchOpen (S) (e)) := by
  apply (completeIdentityFirstRightToGraphChart_isPullback K n h).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (o).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id]
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]

/-- The original outgoing source coordinate on the full graph chart. -/
def completeIdentityFirstChartSourceX : Γ((H), ⊤) :=
  (s).appTop ((Scheme.ΓSpecIso (.of (ChartRing (e)))).inv (leftCoordinate (e)))

/-- The original incoming source coordinate on the full graph chart. -/
def completeIdentityFirstChartSourceY : Γ((H), ⊤) :=
  (s).appTop ((Scheme.ΓSpecIso (.of (ChartRing (e)))).inv (rightCoordinate (e)))

/-- The actual outgoing branch is the entire principal open of the original x coordinate. -/
theorem completeIdentityFirstChartSourceX_open :
    (H).basicOpen (completeIdentityFirstChartSourceX K n h) = (l).opensRange := by
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange, CartesianFiniteFibers.range_eq_preimage
    (completeIdentityFirstChartSource_left_isPullback K n h).flip, leftBranchOpen_range]
  rw [completeIdentityFirstChartSourceX, ← Scheme.preimage_basicOpen_top]
  let source : (H) ⟶ Spec (.of (ChartRing (e))) := (s)
  exact congrArg (fun V : (Spec (.of (ChartRing (e)))).Opens ↦
    source ⁻¹' (V : Set _)) (basicOpen_eq_of_affine (R := .of (ChartRing (e)))
      (leftCoordinate (e)))

/-- The actual incoming branch is the entire principal open of the original y coordinate. -/
theorem completeIdentityFirstChartSourceY_open :
    (H).basicOpen (completeIdentityFirstChartSourceY K n h) = (r).opensRange := by
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange, CartesianFiniteFibers.range_eq_preimage
    (completeIdentityFirstChartSource_right_isPullback K n h).flip, rightBranchOpen_range]
  rw [completeIdentityFirstChartSourceY, ← Scheme.preimage_basicOpen_top]
  let source : (H) ⟶ Spec (.of (ChartRing (e))) := (s)
  exact congrArg (fun V : (Spec (.of (ChartRing (e)))).Opens ↦
    source ⁻¹' (V : Set _)) (basicOpen_eq_of_affine (R := .of (ChartRing (e)))
      (rightCoordinate (e)))

end FLT.Mazur.PolygonInfinitesimalStages

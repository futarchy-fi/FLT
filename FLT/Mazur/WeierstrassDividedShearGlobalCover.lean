/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearGlobalInfinityLift
public import FLT.Mazur.SchemeOpenChartRange

/-!
# The original overlap and the translated global cover

The infinity lift and the inverse local shear have exactly the original
boundary as their intersection, and cover the entire sheared finite model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (r : R)
  (j : ℕ) (hj : j ≤ n)
local notation "dat" => fun a => shearData (data a) r
local notation "U" => rootShearCurve W r
local notation "C" => WeierstrassCurve.VariableChange.mk (1 : Rˣ) 0 r 0
local notation "i" => integralVariableChangeIso W U C rfl
local notation "m" => shearFiniteModificationIso hπ data r j hj
local notation "f" => finiteGlobalContraction hπ dat j hj ≫ Iso.hom i

local notation "l" => shearFiniteInfinityLift hπ data r j hj
local notation "q" => Iso.inv m ≫ finiteLocalChart hπ dat j hj

/-- The original boundary remains the full intersection of the two comparison charts. -/
theorem shearFiniteGlobal_overlap_isPullback :
    IsPullback (affineBoundaryToY W) (finiteYBoundary hπ data j hj) (l) (q) := by
  have H := (finiteYBoundary_isPullback hπ data j hj).paste_horiz (yz_isPullback W)
  simp only [Category.id_comp, finiteToAffine_toCurve] at H
  have H' : IsPullback (affineBoundaryToY W ≫ 𝟙 _) (finiteYBoundary hπ data j hj)
      (integralCurveChart W 1) ((q) ≫ (f)) := by
    simpa only [Category.comp_id, Category.assoc, shearFiniteLocalInv_contraction] using H
  exact H'.of_right (shearFiniteInfinityLift_overlap hπ data r j hj)
    (shearFiniteInfinityLift_isPullback hπ data r j hj)

/-- The comparison infinity chart contains the entire preimage of the original Y-chart. -/
theorem shearFiniteInfinityLift_range :
    Set.range (l) = (f) ⁻¹' Set.range (integralCurveChart W 1) :=
  SchemeOpenChartRange.range_of_isPullback _ _ _ _
    (shearFiniteInfinityLift_isPullback hπ data r j hj)

/-- The unchanged affine chart under shear identifies the full finite local preimage. -/
theorem shearFiniteLocalInv_range :
    Set.range (q) = (f) ⁻¹' Set.range (integralCurveChart W 2) :=
  SchemeOpenChartRange.range_iso_comp_preimage (m).symm _ _ _
    (integralCurveChart U 2).opensRange (integralCurveChart W 2).opensRange
    (SchemeOpenChartRange.range_of_isPullback _ _ _ _ (finiteLocal_isPullback hπ dat j hj))
    (integralShear_affine_preimage W r)

/-- The lifted infinity chart and the inverse local shear cover the whole sheared global model. -/
theorem shearFiniteGlobal_charts_cover (z : finiteGlobalModel hπ dat j hj) :
    (∃ a, (l) a = z) ∨ ∃ a, (q) a = z := by
  change z ∈ Set.range (l) ∨ z ∈ Set.range (q)
  rw [shearFiniteInfinityLift_range, shearFiniteLocalInv_range]
  exact integralCurve_yz_cover W ((f) z)

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitCycle

/-!
# Cyclic agreement determines the complete original components

Endpoint reversals are cancelled as source isomorphisms. Agreement therefore
retains every whole branch component, both terminal branches, and the exterior.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
variable {Y : Scheme.{u}}
  (f g : finiteGlobalTensorModel hπ data (ResidueField R) (s + 1) hs ⟶ Y)
  (h : ∀ i, (positiveSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ f =
    (positiveSplitCycleComponent hπ data D s hs hstart hk hp i).left ≫ g)

include h in
/-- Both complete branches are detected, independent of their cyclic orientation. -/
theorem positiveSplitCycleComponent_branch_hom_ext (j : Fin (s + 2)) (i : Fin 2) :
    (positiveSplitBranchComponent hπ data D s hs hstart hk hp j i).left ≫ f =
      (positiveSplitBranchComponent hπ data D s hs hstart hk hp j i).left ≫ g := by
  fin_cases i
  · have H := h ⟨j.val + 1, by omega⟩
    rw [positiveSplitCycleComponent_first] at H
    simp only [Over.comp_left, Category.assoc] at H
    exact (cancel_epi (ProjectiveLine.endpointReversalIso K).hom).mp H
  · have H := h ⟨2 * s + 4 - j.val, by omega⟩
    rwa [positiveSplitCycleComponent_second] at H

include h in
/-- The two original initial projective components are determined in full. -/
theorem positiveSplitCycleComponent_initial_hom_ext (i : Fin 2) :
    finalInitialComponent hπ data D s hs hstart hk i ≫ f =
      finalInitialComponent hπ data D s hs hstart hk i ≫ g := by
  have H := positiveSplitCycleComponent_branch_hom_ext hπ data D s hs hstart hk hp f g h 0 i
  rw [positiveSplitBranchComponent_initial] at H
  exact H

include h in
/-- Every complete original strict branch is recovered after the initial component. -/
theorem positiveSplitCycleComponent_tail_hom_ext (j : Fin (s + 1)) (i : Fin 2) :
    (finalBranchComponent hπ data D s hs hk hp j i).left ≫ f =
      (finalBranchComponent hπ data D s hs hk hp j i).left ≫ g := by
  have H := positiveSplitCycleComponent_branch_hom_ext hπ data D s hs hstart hk hp f g h
    ⟨j.val + 1, by omega⟩ i
  rwa [positiveSplitBranchComponent_tail] at H

include h in
/-- Every complete original adjacent component is determined. -/
theorem positiveSplitCycleComponent_adjacent_hom_ext (j : Fin s) (i : Fin 2) :
    finalAdjacentComponent hπ data D s hs hk j i ≫ f =
      finalAdjacentComponent hπ data D s hs hk j i ≫ g := by
  have H := positiveSplitCycleComponent_tail_hom_ext hπ data D s hs hstart hk hp f g h
    ⟨j.val, by omega⟩ i
  rw [finalBranchComponent_adjacent] at H
  exact H

include h in
/-- The complete incidence line on the original exterior is determined. -/
theorem positiveSplitCycleComponent_incidence_hom_ext :
    initialGlobalIncidenceLine hπ data D (s + 1) hs hstart (by omega) ≫ f =
      initialGlobalIncidenceLine hπ data D (s + 1) hs hstart (by omega) ≫ g := by
  have H := congrArg (fun q =>
    initialExteriorAffineChart hπ data D (s + 1) hs hstart (by omega) ≫
      (initialExteriorOrientedIso hπ data D (s + 1) hs hstart (by omega) (by omega)).hom ≫ q)
    (h 0)
  simpa only [positiveSplitCycleComponent_exterior,
    equalityInitialExteriorOverComponent_original_assoc, initialExteriorToGlobal_affine_assoc]
    using H

end FLT.Mazur.WeierstrassDividedDepth

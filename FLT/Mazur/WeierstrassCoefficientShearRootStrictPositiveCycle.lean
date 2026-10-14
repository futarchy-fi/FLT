/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootStrictPositiveBranches
public import FLT.Mazur.WeierstrassDividedPositiveSplitCycle

/-!
# Independent complete components in the strict positive-start cycle

Combine the independently glued initial and adjacent pairs with the existing
complete exterior and both terminal components. Retain the original strict cycle.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
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
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs
local notation "E" => coefficientShearGluedOverIso hπ data K 0 (s + 1) hs
local notation "ρ" => Iso.hom (ProjectiveLine.endpointReversalOverIso K)
local notation "C" => coefficientShearRootStrictPositiveBranchComponent
  hπ data D s hs hstart hk hp
local notation "N" => finalNodeOverSection hπ data D s hs hk hp

/-- The original exterior closes the two independent chains in the actual cyclic order. -/
def coefficientShearRootStrictPositiveCycleComponent (i : Fin (2 * s + 5)) :
    PolygonPinching.component K ⟶ Over.mk p :=
  if h0 : i.val = 0 then
    equalityInitialExteriorOverComponent hπ data D s hs hstart hk ≫ (E).inv
  else if h : i.val ≤ s + 2 then ρ ≫ C ⟨i.val - 1, by omega⟩ 0
  else C ⟨2 * s + 4 - i.val, by omega⟩ 1

/-- Every complete component reconstructs the original at precisely the same cyclic position. -/
@[reassoc] theorem coefficientShearRootStrictPositiveCycleComponent_original (i : Fin (2 * s + 5)) :
    coefficientShearRootStrictPositiveCycleComponent hπ data D s hs hstart hk hp i ≫ (E).hom =
      positiveSplitCycleComponent hπ data D s hs hstart hk hp i := by
  unfold coefficientShearRootStrictPositiveCycleComponent positiveSplitCycleComponent
  split_ifs
  · rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [Category.assoc, coefficientShearRootStrictPositiveBranchComponent_original]
  · exact coefficientShearRootStrictPositiveBranchComponent_original hπ data D s hs hstart hk hp _ 1

/-- The component at zero is exactly the original exterior in the reconstructed model. -/
theorem coefficientShearRootStrictPositiveCycleComponent_exterior :
    coefficientShearRootStrictPositiveCycleComponent hπ data D s hs hstart hk hp 0 =
      equalityInitialExteriorOverComponent hπ data D s hs hstart hk ≫ (E).inv := by
  simp only [coefficientShearRootStrictPositiveCycleComponent, Fin.val_zero, dite_true]

/-- The full first chain occurs with reversed endpoints and unchanged retained levels. -/
theorem coefficientShearRootStrictPositiveCycleComponent_first (j : Fin (s + 2)) :
    coefficientShearRootStrictPositiveCycleComponent hπ data D s hs hstart hk hp
        ⟨j.val + 1, by omega⟩ = ρ ≫ C j 0 := by
  apply (cancel_mono (E).hom).mp
  rw [coefficientShearRootStrictPositiveCycleComponent_original, Category.assoc,
    coefficientShearRootStrictPositiveBranchComponent_original, positiveSplitCycleComponent_first]

/-- The full second chain retains its parameter while traversing the cycle in decreasing order. -/
theorem coefficientShearRootStrictPositiveCycleComponent_second (j : Fin (s + 2)) :
    coefficientShearRootStrictPositiveCycleComponent hπ data D s hs hstart hk hp
        ⟨2 * s + 4 - j.val, by omega⟩ = C j 1 := by
  apply (cancel_mono (E).hom).mp
  rw [coefficientShearRootStrictPositiveCycleComponent_original,
    coefficientShearRootStrictPositiveBranchComponent_original, positiveSplitCycleComponent_second]

/-- Zero is the original actual node at the same cyclic position. -/
@[reassoc] theorem coefficientShearRootStrictPositiveCycleComponent_zero (i : Fin (2 * s + 5)) :
    ProjectiveLine.zeroSection K ≫
        coefficientShearRootStrictPositiveCycleComponent hπ data D s hs hstart hk hp i =
      N (positiveSplitCycleNodeIndex start s hstart i) ≫ (E).inv := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, coefficientShearRootStrictPositiveCycleComponent_original,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, positiveSplitCycleComponent_zero]

/-- Infinity on the successor is the same actual node, including the cyclic wrap. -/
@[reassoc] theorem coefficientShearRootStrictPositiveCycleComponent_next_infinity
    (i : Fin (2 * s + 5)) :
    ProjectiveLine.infinitySection K ≫
        coefficientShearRootStrictPositiveCycleComponent hπ data D s hs hstart hk hp
          (PolygonPinching.next (by omega) i) =
      N (positiveSplitCycleNodeIndex start s hstart i) ≫ (E).inv := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, coefficientShearRootStrictPositiveCycleComponent_original,
    Category.assoc, Iso.inv_hom_id, Category.comp_id,
    positiveSplitCycleComponent_next_infinity]

/-- The independent full component cycle satisfies the original pinching endpoint convention. -/
theorem coefficientShearRootStrictPositiveCycleComponent_endpoints (i : Fin (2 * s + 5)) :
    ProjectiveLine.zeroSection K ≫
        coefficientShearRootStrictPositiveCycleComponent hπ data D s hs hstart hk hp i =
      ProjectiveLine.infinitySection K ≫
        coefficientShearRootStrictPositiveCycleComponent hπ data D s hs hstart hk hp
          (PolygonPinching.next (by omega) i) := by
  rw [coefficientShearRootStrictPositiveCycleComponent_zero,
    coefficientShearRootStrictPositiveCycleComponent_next_infinity]

end FLT.Mazur.WeierstrassDividedDepth

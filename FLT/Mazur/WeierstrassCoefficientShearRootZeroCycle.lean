/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootFinalBranches
public import FLT.Mazur.WeierstrassDividedZeroSplitCycle

/-!
# The complete independent branch cycle in the coefficient model

At start zero and strict terminal depth, combine both independently glued
chains with the original exterior. Compare all cyclic components and nodes.
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
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs
local notation "E" => coefficientShearGluedOverIso hπ data K 0 (s + 1) hs
local notation "ρ" => Iso.hom (ProjectiveLine.endpointReversalOverIso K)
local notation "C" => coefficientShearRootFinalBranchComponent hπ data D s hs hk hp
local notation "N" => coefficientShearFinalNodeOverSection hπ data D s hs hk hp

/-- The original exterior closes the two independent chains in the actual cyclic order. -/
def coefficientShearRootZeroCycleComponent (i : Fin (2 * s + 3)) :
    PolygonPinching.component K ⟶ Over.mk p :=
  if i.val = 0 then finalZeroExteriorOverComponent hπ data D s hs hstart hk ≫ (E).inv
  else if h : i.val ≤ s + 1 then ρ ≫ C ⟨i.val - 1, by omega⟩ 0
  else C ⟨2 * s + 2 - i.val, by omega⟩ 1

/-- Every complete component reconstructs the original at precisely the same cyclic position. -/
@[reassoc] theorem coefficientShearRootZeroCycleComponent_original (i : Fin (2 * s + 3)) :
    coefficientShearRootZeroCycleComponent hπ data D s hs hstart hk hp i ≫ (E).hom =
      zeroSplitCycleComponent hπ data D s hs hstart hk hp i := by
  unfold coefficientShearRootZeroCycleComponent zeroSplitCycleComponent
  split_ifs
  · rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [Category.assoc, coefficientShearRootFinalBranchComponent_original]
  · exact coefficientShearRootFinalBranchComponent_original hπ data D s hs hk hp _ 1

/-- The component at zero is exactly the original exterior in the reconstructed model. -/
theorem coefficientShearRootZeroCycleComponent_exterior :
    coefficientShearRootZeroCycleComponent hπ data D s hs hstart hk hp 0 =
      finalZeroExteriorOverComponent hπ data D s hs hstart hk ≫ (E).inv := by
  simp only [coefficientShearRootZeroCycleComponent, Fin.val_zero, ite_true]

/-- The full first chain occurs with reversed endpoints and unchanged retained levels. -/
theorem coefficientShearRootZeroCycleComponent_first (j : Fin (s + 1)) :
    coefficientShearRootZeroCycleComponent hπ data D s hs hstart hk hp
        ⟨j.val + 1, by omega⟩ = ρ ≫ C j 0 := by
  apply (cancel_mono (E).hom).mp
  rw [coefficientShearRootZeroCycleComponent_original, Category.assoc,
    coefficientShearRootFinalBranchComponent_original, zeroSplitCycleComponent_first]

/-- The full second chain retains its parameter while traversing the cycle in decreasing order. -/
theorem coefficientShearRootZeroCycleComponent_second (j : Fin (s + 1)) :
    coefficientShearRootZeroCycleComponent hπ data D s hs hstart hk hp
        ⟨2 * s + 2 - j.val, by omega⟩ = C j 1 := by
  apply (cancel_mono (E).hom).mp
  rw [coefficientShearRootZeroCycleComponent_original,
    coefficientShearRootFinalBranchComponent_original, zeroSplitCycleComponent_second]

/-- Zero is the original actual node at the same cyclic position. -/
@[reassoc] theorem coefficientShearRootZeroCycleComponent_zero (i : Fin (2 * s + 3)) :
    ProjectiveLine.zeroSection K ≫
        coefficientShearRootZeroCycleComponent hπ data D s hs hstart hk hp i =
      N (zeroSplitCycleNodeIndex start s i) := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, coefficientShearRootZeroCycleComponent_original,
    coefficientShearFinalNodeOverSection_original, zeroSplitCycleComponent_zero]

/-- Infinity on the successor is the same actual node, including the cyclic wrap. -/
@[reassoc] theorem coefficientShearRootZeroCycleComponent_next_infinity
    (i : Fin (2 * s + 3)) :
    ProjectiveLine.infinitySection K ≫
        coefficientShearRootZeroCycleComponent hπ data D s hs hstart hk hp
          (PolygonPinching.next (by omega) i) = N (zeroSplitCycleNodeIndex start s i) := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, coefficientShearRootZeroCycleComponent_original,
    coefficientShearFinalNodeOverSection_original, zeroSplitCycleComponent_next_infinity]

/-- The independent full component cycle satisfies the original pinching endpoint convention. -/
theorem coefficientShearRootZeroCycleComponent_endpoints (i : Fin (2 * s + 3)) :
    ProjectiveLine.zeroSection K ≫
        coefficientShearRootZeroCycleComponent hπ data D s hs hstart hk hp i =
      ProjectiveLine.infinitySection K ≫
        coefficientShearRootZeroCycleComponent hπ data D s hs hstart hk hp
          (PolygonPinching.next (by omega) i) := by
  rw [coefficientShearRootZeroCycleComponent_zero,
    coefficientShearRootZeroCycleComponent_next_infinity]

end FLT.Mazur.WeierstrassDividedDepth

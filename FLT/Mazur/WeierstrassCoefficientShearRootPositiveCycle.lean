/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootPositiveBranches
public import FLT.Mazur.WeierstrassDividedPositiveEqualityCycle

/-!
# Independent positive branches in the original equality-depth cycle

Combine the independently glued initial and adjacent pairs with the existing
complete exterior and nonsingular terminal component. Retain the original cycle.
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
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs
local notation "E" => coefficientShearGluedOverIso hπ data K 0 (s + 1) hs
local notation "ρ" => Iso.hom (ProjectiveLine.endpointReversalOverIso K)
local notation "C" => coefficientShearRootPositiveBranchComponent hπ data D s hs hstart hk
local notation "N" => equalityNodeOverSection hπ data D s hs hk

/-- The original exterior closes the two independent chains in the actual cyclic order. -/
def coefficientShearRootPositiveCycleComponent (i : Fin (2 * s + 4)) :
    PolygonPinching.component K ⟶ Over.mk p :=
  if h0 : i.val = 0 then
    equalityInitialExteriorOverComponent hπ data D s hs hstart hk ≫ (E).inv
  else if h : i.val ≤ s + 1 then ρ ≫ C ⟨i.val - 1, by omega⟩ 0
  else if ht : i.val = s + 2 then
    ρ ≫ equalityTerminalOverComponent hπ data D s hs hk hp ≫ (E).inv
  else C ⟨2 * s + 3 - i.val, by omega⟩ 1

/-- Every complete component reconstructs the original at precisely the same cyclic position. -/
@[reassoc] theorem coefficientShearRootPositiveCycleComponent_original (i : Fin (2 * s + 4)) :
    coefficientShearRootPositiveCycleComponent hπ data D s hs hstart hk hp i ≫ (E).hom =
      positiveEqualityCycleComponent hπ data D s hs hstart hk hp i := by
  unfold coefficientShearRootPositiveCycleComponent positiveEqualityCycleComponent
  split_ifs
  · rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [Category.assoc, coefficientShearRootPositiveBranchComponent_original]
  · simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · exact coefficientShearRootPositiveBranchComponent_original hπ data D s hs hstart hk _ 1

/-- The component at zero is exactly the original exterior in the reconstructed model. -/
theorem coefficientShearRootPositiveCycleComponent_exterior :
    coefficientShearRootPositiveCycleComponent hπ data D s hs hstart hk hp 0 =
      equalityInitialExteriorOverComponent hπ data D s hs hstart hk ≫ (E).inv := by
  simp only [coefficientShearRootPositiveCycleComponent, Fin.val_zero, dite_true]

/-- The full first chain occurs with reversed endpoints and unchanged retained levels. -/
theorem coefficientShearRootPositiveCycleComponent_first (j : Fin (s + 1)) :
    coefficientShearRootPositiveCycleComponent hπ data D s hs hstart hk hp
        ⟨j.val + 1, by omega⟩ = ρ ≫ C j 0 := by
  apply (cancel_mono (E).hom).mp
  rw [coefficientShearRootPositiveCycleComponent_original, Category.assoc,
    coefficientShearRootPositiveBranchComponent_original, positiveEqualityCycleComponent_first]

/-- The full second chain retains its parameter while traversing the cycle in decreasing order. -/
theorem coefficientShearRootPositiveCycleComponent_second (j : Fin (s + 1)) :
    coefficientShearRootPositiveCycleComponent hπ data D s hs hstart hk hp
        ⟨2 * s + 3 - j.val, by omega⟩ = C j 1 := by
  apply (cancel_mono (E).hom).mp
  rw [coefficientShearRootPositiveCycleComponent_original,
    coefficientShearRootPositiveBranchComponent_original, positiveEqualityCycleComponent_second]

/-- The unique terminal position retains the full original nonsingular projective component. -/
theorem coefficientShearRootPositiveCycleComponent_terminal :
    coefficientShearRootPositiveCycleComponent hπ data D s hs hstart hk hp
        ⟨s + 2, by omega⟩ =
      ρ ≫ equalityTerminalOverComponent hπ data D s hs hk hp ≫ (E).inv := by
  apply (cancel_mono (E).hom).mp
  simp only [coefficientShearRootPositiveCycleComponent_original, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, positiveEqualityCycleComponent_terminal]

/-- Zero is the original actual node at the same cyclic position. -/
@[reassoc] theorem coefficientShearRootPositiveCycleComponent_zero (i : Fin (2 * s + 4)) :
    ProjectiveLine.zeroSection K ≫
        coefficientShearRootPositiveCycleComponent hπ data D s hs hstart hk hp i =
      N (positiveEqualityCycleNodeIndex start s hstart i) ≫ (E).inv := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, coefficientShearRootPositiveCycleComponent_original,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, positiveEqualityCycleComponent_zero]

/-- Infinity on the successor is the same actual node, including the cyclic wrap. -/
@[reassoc] theorem coefficientShearRootPositiveCycleComponent_next_infinity
    (i : Fin (2 * s + 4)) :
    ProjectiveLine.infinitySection K ≫
        coefficientShearRootPositiveCycleComponent hπ data D s hs hstart hk hp
          (PolygonPinching.next (by omega) i) =
      N (positiveEqualityCycleNodeIndex start s hstart i) ≫ (E).inv := by
  apply (cancel_mono (E).hom).mp
  rw [Category.assoc, coefficientShearRootPositiveCycleComponent_original,
    Category.assoc, Iso.inv_hom_id, Category.comp_id,
    positiveEqualityCycleComponent_next_infinity]

/-- The independent full component cycle satisfies the original pinching endpoint convention. -/
theorem coefficientShearRootPositiveCycleComponent_endpoints (i : Fin (2 * s + 4)) :
    ProjectiveLine.zeroSection K ≫
        coefficientShearRootPositiveCycleComponent hπ data D s hs hstart hk hp i =
      ProjectiveLine.infinitySection K ≫
        coefficientShearRootPositiveCycleComponent hπ data D s hs hstart hk hp
          (PolygonPinching.next (by omega) i) := by
  rw [coefficientShearRootPositiveCycleComponent_zero,
    coefficientShearRootPositiveCycleComponent_next_infinity]

end FLT.Mazur.WeierstrassDividedDepth

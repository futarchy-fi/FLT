/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalSections
public import FLT.Mazur.WeierstrassDividedOlderGlobalExterior
public import FLT.Mazur.WeierstrassSuccessiveXResidueIncidenceBoundary

/-!
# The ordered retained node sections miss the entire preceding exterior

The full horizontal intersection transports local vanishing to the actual global
model at every later retention. No preceding component can contain either node.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "i" => olderGlobalExteriorTensorChart hπ data K j hj r hr
local notation "g" => olderGlobalTensorChart hπ data K j hj r hr
local notation "u" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "first" => olderGlobalFirstSection hπ data D j hj r hr hk0 hk
local notation "second" => olderGlobalSecondSection hπ data D j hj r hr hk0 hk

/-- The full preceding exterior has empty scheme intersection with the first retained node. -/
theorem olderGlobalFirstSectionExterior_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) i first := by
  have H := (residueFirstIncidenceBoundary_isPullback D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) 2).paste_horiz
      (olderGlobalExteriorTensor_isPullback hπ data K j hj r hr)
  simpa only [Scheme.eq_emptyTo, olderGlobalFirstSection] using H

/-- No preceding exterior point is the first retained node. -/
theorem olderGlobalFirstSectionExterior_disjoint :
    Disjoint (Set.range i) (Set.range first) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨v, _, _⟩ := Scheme.exists_preimage_of_isPullback
    (olderGlobalFirstSectionExterior_isPullback hπ data D j hj r hr hk0 hk) a b hb.symm
  exact isEmptyElim v

/-- The first section has empty preimage of the entire preceding exterior. -/
theorem olderGlobalFirstSectionExterior_preimage : first ⁻¹' Set.range i = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact Set.disjoint_left.mp
    (olderGlobalFirstSectionExterior_disjoint hπ data D j hj r hr hk0 hk) hz ⟨z, rfl⟩

/-- The full preceding exterior has empty scheme intersection with the second retained node. -/
theorem olderGlobalSecondSectionExterior_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) i second := by
  have H := (residueSecondIncidenceBoundary_isPullback D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) 2 (by decide)).paste_horiz
      (olderGlobalExteriorTensor_isPullback hπ data K j hj r hr)
  simpa only [Scheme.eq_emptyTo, olderGlobalSecondSection] using H

/-- No preceding exterior point is the second retained node. -/
theorem olderGlobalSecondSectionExterior_disjoint :
    Disjoint (Set.range i) (Set.range second) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨v, _, _⟩ := Scheme.exists_preimage_of_isPullback
    (olderGlobalSecondSectionExterior_isPullback hπ data D j hj r hr hk0 hk) a b hb.symm
  exact isEmptyElim v

/-- The second section has empty preimage of the entire preceding exterior. -/
theorem olderGlobalSecondSectionExterior_preimage : second ⁻¹' Set.range i = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact Set.disjoint_left.mp
    (olderGlobalSecondSectionExterior_disjoint hπ data D j hj r hr hk0 hk) hz ⟨z, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth

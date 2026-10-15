/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticInitialNodeIntersection
public import FLT.Mazur.WeierstrassModificationXArithmeticNodeSeparation

/-!
# Wrong-label initial full nodes and first arithmetic branches do not meet

The full original tensor pullback reduces every candidate intersection to
its constructed Laurent boundary, which misses the wrong full initial node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
  (h1 : 1 ≤ n) (r : ℕ) (hr : 1 + r ≤ n)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ start) (h2 : π ∣ W.a₂)
  (hd3 : π ∣ (data ⟨0, Nat.zero_lt_succ n⟩).b3)
  (hd4 : π ∣ (data ⟨0, Nat.zero_lt_succ n⟩).b4)
  (hd6 : π ∣ (data ⟨0, Nat.zero_lt_succ n⟩).b6)
  (he3 : π ∣ (data ⟨1, Nat.lt_succ_of_le h1⟩).b3)
  (he4 : π ∣ (data ⟨1, Nat.lt_succ_of_le h1⟩).b4)
  (he6 : π ∣ (data ⟨1, Nat.lt_succ_of_le h1⟩).b6) (label other : Bool) (hne : label ≠ other)
local notation "c" => arithmeticTensorBranchChart π m W (π ^ start)
  (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hs h2 he3 he4 he6 other
local notation "i" => finiteArithmeticInitialTensorChart hπ data m (1 + r) hr
local notation "a" => finiteArithmeticOlderTensorChart hπ data m 0 h1 r hr
local notation "G" => arithmeticInitialNodeRestriction π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 hd3 hd4 hd6 hs
local notation "B" => initialArithmeticBranchBoundary hπ data m h1 ha hs h2 he3 he4 he6 other
local notation "N" => ite (label = true)
  (arithmeticOppositeInitialTensorNodeChart π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 hd3 hd4 hd6)
  (arithmeticInitialTensorNodeChart π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha h2 hd3 hd4 hd6)

include hne in
/-- A full initial node misses the complete first branch of the other Boolean label. -/
theorem initialArithmeticNodes_crossLabel_disjoint :
    Disjoint (Set.range (N ≫ i)) (Set.range (c ≫ a)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have H := initialArithmeticBranch_isPullback hπ data m h1 r hr
    ha hs h2 he3 he4 he6 other
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback H (N x) y hy.symm
  rw [← initialArithmeticNode_boundary hπ data m h1 ha hs h2
    hd3 hd4 hd6 he3 he4 he6 other] at hz
  exact Set.disjoint_left.mp (arithmeticInitialBoundary_crossLabel_disjoint
    π m W (π ^ start) (Data.b3 d) (Data.b4 d) (Data.b6 d)
    ha hs h2 hd3 hd4 hd6 other label (Ne.symm hne))
    ⟨z, hz⟩ ⟨x, by cases label <;> rfl⟩

include hne in
/-- The complete wrong-label initial/first-branch fiber product is the empty scheme. -/
theorem initialArithmeticNodes_crossLabel_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) (N ≫ i) (c ≫ a) := by
  let _ := Scheme.isEmpty_pullback (N ≫ i) (c ≫ a)
    (initialArithmeticNodes_crossLabel_disjoint hπ data m h1 r hr ha hs h2
      hd3 hd4 hd6 he3 he4 he6 label other hne)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (N ≫ i) (c ≫ a))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentFactorization
public import FLT.Mazur.WeierstrassSuccessiveArithmeticBranchSeparation

/-!
# Full adjacent arithmetic branches of different labels do not meet

The full original adjacent tensor intersection factors through the matching
older branch. Separation of its two complete labels excludes every wrong edge.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + j)) (h2 : π ∣ W.a₂)
  (hd3 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3)
  (hd4 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4)
  (hd6 : π ∣ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6)
  (he3 : π ∣ (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b3)
  (he4 : π ∣ (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b4)
  (he6 : π ∣ (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b6)
  (hsNext : π ∣ π ^ (start + (j + 1))) (a b : Bool) (hab : a ≠ b)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "e" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
variable (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "c₀" => arithmeticTensorBranchChart π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 hd3 hd4 hd6 a
local notation "c₁" => arithmeticTensorBranchChart π m W (π ^ (start + (j + 1)))
  (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hsNext h2 he3 he4 he6 b
local notation "old" => finiteArithmeticAdjacentOldTensorChart hπ data m j hj r hr
local notation "next" => finiteArithmeticOlderTensorChart hπ data m (j + 1) hjNext r hr

include hab in
/-- Adjacent complete arithmetic branches with different Boolean labels have disjoint images. -/
theorem adjacentArithmeticBranches_crossLabel_disjoint :
    Disjoint (Set.range (c₀ ≫ old)) (Set.range (c₁ ≫ next)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  have H := adjacentArithmeticBranch_isPullback hπ data m j hj hjNext r hr
    ha hsNext h2 he3 he4 he6 b
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback H (c₀ x) y hy.symm
  rw [adjacentArithmeticBranchBoundary_factorization hπ data m j hj hjNext
    ha hs h2 hd3 hd4 hd6 he3 he4 he6 hsNext b] at hz
  exact Set.disjoint_left.mp (arithmeticTensorBranchChart_disjoint π m W (π ^ (start + j))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 hd3 hd4 hd6 a b hab)
    ⟨x, rfl⟩ ⟨((PolygonSmoothing.edgeInversion Q).hom ≫
      PolygonSmoothing.leftBranchOpen Q (parameter R π m)) z, hz⟩

include hab in
/-- The complete wrong-label adjacent fiber product is the empty scheme. -/
theorem adjacentArithmeticBranches_crossLabel_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) (c₀ ≫ old) (c₁ ≫ next) := by
  let _ := Scheme.isEmpty_pullback (c₀ ≫ old) (c₁ ≫ next)
    (adjacentArithmeticBranches_crossLabel_disjoint hπ data m j hj hjNext
      ha hs h2 hd3 hd4 hd6 he3 he4 he6 hsNext a b hab r hr)
  apply IsPullback.of_iso_pullback ⟨Scheme.empty_ext _ _⟩
    (asIso (Scheme.emptyTo (pullback (c₀ ≫ old) (c₁ ≫ next))))
  · exact Scheme.empty_ext _ _
  · exact Scheme.empty_ext _ _

end FLT.Mazur.WeierstrassDividedDepth

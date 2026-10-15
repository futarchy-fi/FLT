/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentTensorSlopeGeometry
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentSlope
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentBranch

/-!
# The actual adjacent arithmetic boundary factors through the older branch

This identifies the previously constructed full tensor-chart boundary with
its correctly labeled older polygon branch. Both integral transitions,
coefficient maps, and the original polygon edge inversion are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R]
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
  (hsNext : π ∣ π ^ (start + (j + 1))) (opposite : Bool)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "e" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "v₀" => arithmeticBranchSlope π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 hd3 hd4 hd6 opposite
local notation "v₁" => arithmeticBranchSlope π m W (π ^ (start + (j + 1)))
  (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hsNext h2 he3 he4 he6 opposite
local notation "h₀" => arithmeticBranchSlope_equation π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 hd3 hd4 hd6 opposite
local notation "h₁" => arithmeticBranchSlope_equation π m W (π ^ (start + (j + 1)))
  (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hsNext h2 he3 he4 he6 opposite

/-- The whole original adjacent boundary enters the same labeled older arithmetic branch. -/
@[reassoc] theorem adjacentArithmeticBranchBoundary_factorization :
    adjacentArithmeticBranchBoundary hπ data m j hj hjNext
      ha hsNext h2 he3 he4 he6 opposite =
    (PolygonSmoothing.edgeInversion Q).hom ≫
      PolygonSmoothing.leftBranchOpen Q (parameter R π m) ≫
        arithmeticTensorBranchChart π m W (π ^ (start + j))
          (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 hd3 hd4 hd6 opposite := by
  have he := adjacentTensorSlope_factorization hπ (start + j) d e Q v₀ v₁ h₀ h₁
    (arithmeticAdjacentBranchSlope hπ (start + j) d e m ha hs h2
      hd3 hd4 hd6 he3 he4 he6 hsNext opposite)
  rw [arithmeticTensorBranchChart_eq] at he
  exact he

end FLT.Mazur.WeierstrassDividedDepth

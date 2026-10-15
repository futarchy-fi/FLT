/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentIntersection
public import FLT.Mazur.WeierstrassSuccessiveArithmeticBranchBoundary

/-!
# Constructed polygon branches on retained adjacent arithmetic boundaries

The original right Laurent open of either constructed next branch is exactly
its intersection with the older arithmetic tensor chart. This holds at every
later retention depth and keeps both original tensor overlap transitions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open PolygonArithmeticStages
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m : ℕ)
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
open WeierstrassSuccessiveX
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "f" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "u" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 f) (Data.b4 f) (Data.b6 f) 2
local notation "depthEquiv" => depthOverlapEquiv W π (start + j)
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "previousEquiv" => previousBoundaryEquiv hπ e f
local notation "A" => PrincipalOpenTensor.transitionIso Q x t depthEquiv
local notation "B" => PrincipalOpenTensor.transitionIso Q x u previousEquiv
/-- Reorient the full adjacent intersection using the next original boundary coordinate. -/
theorem adjacentArithmeticRightTensor_isPullback :
    IsPullback ((B).hom ≫ (A).inv ≫ PrincipalOpenTensor.inclusion Q t)
      (PrincipalOpenTensor.inclusion Q u)
      (finiteArithmeticAdjacentOldTensorChart hπ data m j hj r hr)
      (finiteArithmeticOlderTensorChart hπ data m (j + 1) hjNext r hr) := by
  exact (adjacentArithmeticTensor_isPullback hπ data m j hj hjNext r hr).of_iso
    (B).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

variable (ha : IsUnit W.a₁) (hs : π ∣ π ^ (start + (j + 1))) (h2 : π ∣ W.a₂)
  (h3 : π ∣ (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b3)
  (h4 : π ∣ (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b4)
  (h6 : π ∣ (data ⟨j + 2, Nat.lt_succ_of_le hjNext⟩).b6) (opposite : Bool)
local notation "c" => arithmeticTensorBranchChart π m W (π ^ (start + (j + 1)))
  (Data.b3 f) (Data.b4 f) (Data.b6 f) ha hs h2 h3 h4 h6 opposite
local notation "β" => arithmeticBranchRightBoundary π m W (π ^ (start + (j + 1)))
  (Data.b3 f) (Data.b4 f) (Data.b6 f) ha hs h2 h3 h4 h6 opposite

/-- The branch boundary retains the actual depth and preceding integral overlap maps. -/
def adjacentArithmeticBranchBoundary : PolygonSmoothing.branchTorus Q ⟶
    Spec (.of (ScalarExtension W (π ^ (start + j)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) Q)) :=
  β ≫ (B).hom ≫ (A).inv ≫ PrincipalOpenTensor.inclusion Q t

/-- The full next right torus is exactly its intersection with the older arithmetic chart. -/
theorem adjacentArithmeticBranch_isPullback :
    IsPullback (adjacentArithmeticBranchBoundary hπ data m j hj hjNext
      ha hs h2 h3 h4 h6 opposite)
      (PolygonSmoothing.rightBranchOpen Q (parameter R π m))
      (finiteArithmeticAdjacentOldTensorChart hπ data m j hj r hr)
      (c ≫ finiteArithmeticOlderTensorChart hπ data m (j + 1) hjNext r hr) :=
  (arithmeticBranchRightBoundary_isPullback π m W (π ^ (start + (j + 1)))
    (Data.b3 f) (Data.b4 f) (Data.b6 f) ha hs h2 h3 h4 h6 opposite).paste_horiz
      (adjacentArithmeticRightTensor_isPullback hπ data m j hj hjNext r hr)

/-- The constructed adjacent boundary square commutes in every retained arithmetic stage. -/
@[reassoc] theorem adjacentArithmeticBranchBoundary_chart :
    adjacentArithmeticBranchBoundary hπ data m j hj hjNext ha hs h2 h3 h4 h6 opposite ≫
      finiteArithmeticAdjacentOldTensorChart hπ data m j hj r hr =
        PolygonSmoothing.rightBranchOpen Q (parameter R π m) ≫
          c ≫ finiteArithmeticOlderTensorChart hπ data m (j + 1) hjNext r hr :=
  (adjacentArithmeticBranch_isPullback hπ data m j hj hjNext r hr
    ha hs h2 h3 h4 h6 opposite).w

/-- The original adjacent Laurent boundary is the whole actual arithmetic fiber product. -/
def adjacentArithmeticBranchPullbackIso :=
  (adjacentArithmeticBranch_isPullback hπ data m j hj hjNext r hr
    ha hs h2 h3 h4 h6 opposite).isoPullback

end FLT.Mazur.WeierstrassDividedDepth

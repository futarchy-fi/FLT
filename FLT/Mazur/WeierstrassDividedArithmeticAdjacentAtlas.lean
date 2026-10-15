/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentFactorization
public import FLT.Mazur.LaurentReciprocalSubstitution

/-!
# Exact adjacent arithmetic branch intersections with the original atlas edge

The intersection is now between the two constructed polygon branches, rather
than the next branch and the full older tensor chart. Reorienting by the
original inversion gives precisely the left/preceding polygon atlas legs.
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
  (hsNext : π ∣ π ^ (start + (j + 1))) (opposite : Bool)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "e" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
variable (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "c₀" => arithmeticTensorBranchChart π m W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 hd3 hd4 hd6 opposite
local notation "c₁" => arithmeticTensorBranchChart π m W (π ^ (start + (j + 1)))
  (Data.b3 e) (Data.b4 e) (Data.b6 e) ha hsNext h2 he3 he4 he6 opposite
local notation "old" => finiteArithmeticAdjacentOldTensorChart hπ data m j hj r hr
local notation "next" => finiteArithmeticOlderTensorChart hπ data m (j + 1) hjNext r hr
local notation "β" => Iso.hom (PolygonSmoothing.edgeInversion Q) ≫
  PolygonSmoothing.leftBranchOpen Q (parameter R π m)

/-- The full next Laurent boundary is precisely the intersection of the two actual branches. -/
theorem adjacentArithmeticBranches_isPullback :
    IsPullback β (PolygonSmoothing.rightBranchOpen Q (parameter R π m))
      (c₀ ≫ old) (c₁ ≫ next) := by
  let _ := arithmeticTensorBranchChart_isOpenImmersion π m W (π ^ (start + j))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ha hs h2 hd3 hd4 hd6 opposite
  have H := adjacentArithmeticBranch_isPullback hπ data m j hj hjNext r hr
    ha hsNext h2 he3 he4 he6 opposite
  rw [adjacentArithmeticBranchBoundary_factorization hπ data m j hj hjNext
    ha hs h2 hd3 hd4 hd6 he3 he4 he6 hsNext opposite] at H
  have H' : IsPullback (𝟙 (PolygonSmoothing.branchTorus Q)) β (β ≫ c₀) c₀ :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  have H'' : IsPullback (β ≫ c₀)
      (PolygonSmoothing.rightBranchOpen Q (parameter R π m)) old (c₁ ≫ next) := by
    simpa only [Category.assoc] using H
  simpa only [Category.id_comp] using (H'.paste_horiz H''.flip).flip

/-- In the original atlas orientation, the exact adjacent legs are left and preceding. -/
theorem adjacentArithmeticAtlas_isPullback :
    IsPullback (PolygonSmoothing.leftBranchOpen Q (parameter R π m))
      (PolygonSmoothing.precedingBranch Q (parameter R π m))
      (c₀ ≫ old) (c₁ ≫ next) := by
  exact (adjacentArithmeticBranches_isPullback hπ data m j hj hjNext
    ha hs h2 hd3 hd4 hd6 he3 he4 he6 hsNext opposite r hr).of_iso
      (PolygonSmoothing.edgeInversion Q) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp [PolygonSmoothing.precedingBranch, ← Category.assoc,
        LaurentUnitPoints.edgeInversion_comp_self]) (by simp) (by simp)

/-- The genuine adjacent branch comparison satisfies the original polygon atlas equation. -/
@[reassoc] theorem adjacentArithmeticAtlas_overlap :
    PolygonSmoothing.leftBranchOpen Q (parameter R π m) ≫ c₀ ≫ old =
      PolygonSmoothing.precedingBranch Q (parameter R π m) ≫ c₁ ≫ next :=
  (adjacentArithmeticAtlas_isPullback hπ data m j hj hjNext
    ha hs h2 hd3 hd4 hd6 he3 he4 he6 hsNext opposite r hr).w

/-- The original atlas edge is the full fiber product of the two arithmetic polygon branches. -/
def adjacentArithmeticAtlasPullbackIso :=
  (adjacentArithmeticAtlas_isPullback hπ data m j hj hjNext
    ha hs h2 hd3 hd4 hd6 he3 he4 he6 hsNext opposite r hr).isoPullback

end FLT.Mazur.WeierstrassDividedDepth

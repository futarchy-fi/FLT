/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedInitialMaps
public import FLT.Mazur.WeierstrassDividedRevisedFirstRetained
public import FLT.Mazur.WeierstrassDividedRetainedChartOpen

/-!
# Full original initial-to-retained equations in the revised target

The first retained normalization has the same exact Laurent parameter as the
initial factor ratio. The final-node correction fixes that arrow even when
there is only one retained node on each arm.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "t" => parameter R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticRetainedFixedSmoothingIso data H m (j + 1) hj
local notation "E" => arithmeticFactorRatioLaurentIso π m W (π ^ 1)
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.scale_div H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "G" => arithmeticInitialNodeRestriction π m W (π ^ 1)
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) H.scale_div
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π m H.scale_div)

include hπ

/-- The first whole-chart normalization retains the exact original Laurent factor ratio. -/
@[reassoc] theorem arithmeticRevisedFirstNormalization_right :
    rightBranchOpen Q t ≫ (N ⟨0, Nat.zero_lt_succ j⟩).hom =
      (E).hom ≫ precedingBranch Q τ := by
  let _ := hn
  have h := arithmeticStartOneRetainedMap_first hπ data H m (j + 1) hj
    (Nat.zero_lt_succ j) false
  rw [arithmeticStartOneRetainedMap_factorization] at h
  unfold arithmeticFactorRatioFirstRetainedMap at h
  have he := (cancel_mono (retainedPolygonMap Q τ (j + 1)
    ⟨0, Nat.zero_lt_succ j⟩ false)).mp h
  rw [he]
  exact arithmeticFirstRetainedFactorRatioChart_right hπ data H m (j + 1) hj
    (Nat.zero_lt_succ j)

/-- The original initial Laurent leg agrees with the full normalized first retained map. -/
@[reassoc] theorem arithmeticOriginalRevisedInitialMap_first_retained (b : Bool) :
    G ≫ arithmeticOriginalRevisedInitialMap data H m j hj u hu b =
      rightBranchOpen Q t ≫ arithmeticOriginalRevisedRetainedMap data H m j hj u hu
        ⟨0, Nat.zero_lt_succ j⟩ b := by
  rw [arithmeticOriginalRevisedInitialMap, ← Category.assoc,
    arithmeticFactorRatioLaurentIso_boundary, Category.assoc,
    arithmeticRevisedPolygon_initial_retained, arithmeticOriginalRevisedRetainedMap,
    ← Category.assoc (rightBranchOpen Q t), arithmeticRevisedFirstNormalization_right hπ,
    Category.assoc]

/-- At first order the original first edge survives the actual closing correction as well. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedInitialMap_first_retained (b : Bool) :
    arithmeticInitialNodeRestriction π 1 W (π ^ 1)
        (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.a2_div
        (H.b3_div _) (H.b4_div _) (H.b6_div _) H.scale_div ≫
      arithmeticOriginalRevisedInitialMap data H 1 j hj u hu b =
        rightBranchOpen (Quotient R π 1) (parameter R π 1) ≫
          arithmeticFirstOriginalRevisedRetainedMap hπ data H j hj u hu
            ⟨0, Nat.zero_lt_succ j⟩ b := by
  rw [arithmeticFirstOriginalRevisedRetainedMap_incoming]
  exact arithmeticOriginalRevisedInitialMap_first_retained hπ data H 1 j hj u hu b

end FLT.Mazur.WeierstrassDividedDepth

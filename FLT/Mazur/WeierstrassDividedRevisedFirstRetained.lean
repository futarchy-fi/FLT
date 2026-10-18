/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedRetainedMaps
public import FLT.Mazur.WeierstrassDividedFirstResidualIncoming
public import FLT.Mazur.WeierstrassDividedRevisedClosingOriginal

/-!
# First-order retained comparisons with their actual closing corrections

Only the last node on each arm is corrected. The correction fixes every
incoming original arrow, so all full consecutive overlaps still commute.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "t" => parameter R π 1
local notation "N" => arithmeticRetainedFixedSmoothingIso data H 1 (j + 1) hj
local notation "A" => arithmeticFirstResidualRetainedIso hπ data H j hj u hu
local notation "O" => twistedRetainedOrientation data H 1
local notation "c" => arithmeticRevisedPolygonRetainedChart data H 1 j hj u hu
local notation "f" => arithmeticOriginalRevisedRetainedMap data H 1 j hj u hu

/-- The full first-order map at each original retained label, with correction only at the end. -/
def arithmeticFirstOriginalRevisedRetainedMap (a : Fin (j + 1)) (b : Bool) :
    PolygonSmoothing.chart Q t ⟶ arithmeticRevisedPolygon data H 1 j hj u hu :=
  (N a).hom ≫ (if a.val = j then A b else Iso.refl _).hom ≫ (O b).hom ≫ c a b

local notation "g" => arithmeticFirstOriginalRevisedRetainedMap hπ data H j hj u hu

instance arithmeticFirstOriginalRevisedRetainedMap_isOpenImmersion
    (a : Fin (j + 1)) (b : Bool) : IsOpenImmersion (g a b) := by
  unfold arithmeticFirstOriginalRevisedRetainedMap
  infer_instance

/-- All nodes below the final depth retain the entire original normalization. -/
theorem arithmeticFirstOriginalRevisedRetainedMap_below (a : Fin (j + 1))
    (ha : a.val < j) (b : Bool) : g a b = f a b := by
  simp only [arithmeticFirstOriginalRevisedRetainedMap,
    ite_eq_right (show a.val ≠ j by omega), Iso.refl_hom, Category.id_comp,
    arithmeticOriginalRevisedRetainedMap]

/-- Even at the corrected final node, the full original incoming map is unchanged. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedRetainedMap_incoming
    (a : Fin (j + 1)) (b : Bool) :
    rightBranchOpen Q t ≫ g a b = rightBranchOpen Q t ≫ f a b := by
  unfold arithmeticFirstOriginalRevisedRetainedMap arithmeticOriginalRevisedRetainedMap
  split_ifs
  · rw [← Category.assoc (rightBranchOpen Q t),
      ← Category.assoc (rightBranchOpen Q t ≫ (N a).hom),
      arithmeticFirstResidualIncoming_fixed, Category.assoc]
  · simp only [Iso.refl_hom, Category.id_comp]

/-- The reciprocal original incoming parameter is unchanged as a morphism as well. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedRetainedMap_preceding
    (a : Fin (j + 1)) (b : Bool) :
    precedingBranch Q t ≫ g a b = precedingBranch Q t ≫ f a b := by
  simp only [precedingBranch, Category.assoc,
    arithmeticFirstOriginalRevisedRetainedMap_incoming]

/-- All consecutive full original retained overlaps commute after the closing corrections. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedRetainedMap_adjacent
    (a : ℕ) (ha : a + 1 < j + 1) (b : Bool) :
    leftBranchOpen Q t ≫ g ⟨a, by omega⟩ b =
      precedingBranch Q t ≫ g ⟨a + 1, ha⟩ b := by
  rw [arithmeticFirstOriginalRevisedRetainedMap_below hπ data H j hj u hu
      ⟨a, by omega⟩ (show a < j by omega),
    arithmeticFirstOriginalRevisedRetainedMap_preceding]
  exact arithmeticOriginalRevisedRetainedMap_adjacent data H 1 j hj u hu hπ a ha b

/-- The last retained map is exactly the restriction of the already constructed closing pair. -/
@[reassoc] theorem arithmeticFirstOriginalRevisedRetainedMap_closing (b : Bool) :
    pushout.inl (leftBranchOpen Q t)
        (arithmeticOriginalClosingBoundary data H 1 j hj b) ≫
      arithmeticFirstOriginalRevisedClosingMap data H j hj u hu hπ b =
        g ⟨j, by omega⟩ b := by
  rw [arithmeticFirstOriginalRevisedClosingMap_retained]
  simp only [arithmeticFirstOriginalRevisedRetainedMap, ↓reduceIte]

end FLT.Mazur.WeierstrassDividedDepth

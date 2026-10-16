/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioLabeledMaps

/-!
# Full corrected initial and infinity compatibility in the original labeled atlas

The constructed maps satisfy both original infinity equations. Consequently,
any extension to the remaining atlas labels has the required full triangle
compatibility, on the actual three original fiber products.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFactorRatioTensorAffineMap arithmeticFactorRatioTensorInfinityMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "P" => polynomialNodeOverlapInclusion
  (W.map (algebraMap R Q)) (algebraMap R Q (π ^ start))
local notation "B" => arithmeticNodeOverlapOpposite π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "I" => arithmeticInitialOverlapToInfinity hπ data m k hk
  H.a1_unit H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "f" => arithmeticFactorRatioLabeledInitialMap data H hπ m k hk
local notation "g" => arithmeticFactorRatioLabeledInfinityMap data H hπ m k hk
local notation "Y" => arithmeticFactorRatioPolygon π m W (π ^ start) H.a1_unit H.scale_div k

/-- The full corrected maps satisfy the first original infinity equation. -/
@[reassoc] theorem arithmeticFactorRatioTriangle_first : I ≫ g = P ≫ f false := by
  rw [← arithmeticFactorRatioOverlapInfinity_eq_atlas hπ data H m k hk]
  exact arithmeticFactorRatioOverlapInfinity_polygon π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)
      (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) H.scale_div
      (H.a3_div data) (H.a4_div data) (H.a6_div data) k

/-- The full corrected maps retain the original opposite restriction on the entire overlap. -/
@[reassoc] theorem arithmeticFactorRatioTriangle_opposite : I ≫ g = B ≫ f true := by
  rw [arithmeticFactorRatioTriangle_first]
  unfold arithmeticFactorRatioLabeledInitialMap
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← Category.assoc, ← Category.assoc, arithmeticTensorNodes_overlap]

attribute [local irreducible] arithmeticFactorRatioLabeledInitialMap
  arithmeticFactorRatioLabeledInfinityMap arithmeticFactorRatioPolygon

/-- Any extension of these constructed charts satisfies the original infinity predicate. -/
theorem arithmeticFactorRatioTriangle_compatible
    (F : ∀ i, arithmeticLabeledAtlasObject hπ data H m k hk i ⟶ Y)
    (hi : F .infinity = g) (hn : ∀ b, F (.initial b) = f b) :
    arithmeticInitialInfinityCompatible hπ data H m k hk F := by
  constructor
  · rw [hi, hn]
    exact arithmeticFactorRatioTriangle_first hπ data H m k hk
  · rw [hi, hn]
    exact arithmeticFactorRatioTriangle_opposite hπ data H m k hk

/-- The initial pair is compatible on its full original labeled fiber product. -/
theorem arithmeticFactorRatioTriangle_initial_pullback
    (F : ∀ i, arithmeticLabeledAtlasObject hπ data H m k hk i ⟶ Y)
    (hi : F .infinity = g) (hn : ∀ b, F (.initial b) = f b) :
    pullback.fst (arithmeticLabeledAtlasMap hπ data H m k hk (.initial false))
      (arithmeticLabeledAtlasMap hπ data H m k hk (.initial true)) ≫ F (.initial false) =
    pullback.snd (arithmeticLabeledAtlasMap hπ data H m k hk (.initial false))
      (arithmeticLabeledAtlasMap hπ data H m k hk (.initial true)) ≫ F (.initial true) :=
  arithmeticInitialInfinity_initial_compatible hπ data H m k hk F
    (arithmeticFactorRatioTriangle_compatible hπ data H m k hk F hi hn)

end FLT.Mazur.WeierstrassDividedDepth

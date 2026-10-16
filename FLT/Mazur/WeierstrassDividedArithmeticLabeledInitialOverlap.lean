/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAtlas
public import FLT.Mazur.WeierstrassDividedArithmeticInitialInfinity

/-!
# The complete initial overlaps in the labeled arithmetic cover

The two full initial nodes meet along standard D(q). Both meet the original
infinity chart along the same full open, retaining all three actual chart maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "P" => polynomialNodeOverlapInclusion
  (W.map (algebraMap R Q)) (algebraMap R Q (π ^ start))
local notation "B" => arithmeticNodeOverlapOpposite π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "I" => arithmeticInitialOverlapToInfinity hπ data m k hk
  H.a1_unit H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "c" => arithmeticLabeledAtlasMap hπ data H m k hk

/-- The two initial labels in the full atlas have exactly the standard D(q) intersection. -/
theorem arithmeticLabeledAtlas_initial_isPullback :
    IsPullback P B (c (.initial false)) (c (.initial true)) := by
  simpa only [arithmeticLabeledAtlasMap, arithmeticLabeledInitialChart,
    Bool.false_eq_true, ↓reduceIte] using
    initialArithmeticNodes_isPullback hπ data m k hk
      H.a1_unit H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- The first initial label meets the original infinity chart along its full standard D(q). -/
theorem arithmeticLabeledAtlas_first_infinity_isPullback :
    IsPullback I P (c .infinity) (c (.initial false)) := by
  simpa only [arithmeticLabeledAtlasMap, arithmeticLabeledInitialChart,
    arithmeticTensorAtlasMap, globalTensorAtlasMap, Fin.cases_zero,
    Bool.false_eq_true, ↓reduceIte] using
    arithmeticFirstNode_infinity_isPullback hπ data m k hk
      H.a1_unit H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- The opposite label meets infinity in the same complete open, with its actual second leg. -/
theorem arithmeticLabeledAtlas_opposite_infinity_isPullback :
    IsPullback I B (c .infinity) (c (.initial true)) := by
  simpa only [arithmeticLabeledAtlasMap, arithmeticLabeledInitialChart,
    arithmeticTensorAtlasMap, globalTensorAtlasMap, Fin.cases_zero, ↓reduceIte] using
    arithmeticOppositeNode_infinity_isPullback hπ data m k hk
      H.a1_unit H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- All three original labeled chart maps agree on the complete initial overlap. -/
theorem arithmeticLabeledAtlas_initial_triangle :
    P ≫ c (.initial false) = B ≫ c (.initial true) ∧
      I ≫ c .infinity = P ≫ c (.initial false) :=
  ⟨(arithmeticLabeledAtlas_initial_isPullback hπ data H m k hk).w,
    (arithmeticLabeledAtlas_first_infinity_isPullback hπ data H m k hk).w⟩

end FLT.Mazur.WeierstrassDividedDepth

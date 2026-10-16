/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledInitialOverlap

/-!
# Compatibility on the full initial and infinity triangle

The two original infinity equations imply the initial-initial equation.
Every comparison uses the actual full standard D(q) intersection.
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

variable {Y : Scheme.{0}}
  (f : ∀ i, arithmeticLabeledAtlasObject hπ data H m k hk i ⟶ Y)
local notation "C" => fun (i j : ArithmeticChartLabel k) => pullback.fst (c i) (c j) ≫ f i =
  pullback.snd (c i) (c j) ≫ f j

/-- The two equations on the original common infinity puncture. -/
def arithmeticInitialInfinityCompatible : Prop :=
  I ≫ f .infinity = P ≫ f (.initial false) ∧
    I ≫ f .infinity = B ≫ f (.initial true)

/-- The first original infinity equation detects its complete labeled fiber product. -/
theorem arithmeticInitialInfinity_first_iff :
    C .infinity (.initial false) ↔ I ≫ f .infinity = P ≫ f (.initial false) := by
  dsimp only
  have T := arithmeticLabeledAtlas_first_infinity_isPullback hπ data H m k hk
  rw [← cancel_epi T.isoPullback.hom]
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]

/-- The opposite infinity equation retains its exact original second restriction. -/
theorem arithmeticInitialInfinity_opposite_iff :
    C .infinity (.initial true) ↔ I ≫ f .infinity = B ≫ f (.initial true) := by
  dsimp only
  have T := arithmeticLabeledAtlas_opposite_infinity_isPullback hπ data H m k hk
  rw [← cancel_epi T.isoPullback.hom]
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]

/-- Both full initial labels are compatible as a consequence of the two infinity equations. -/
theorem arithmeticInitialInfinity_initial_compatible
    (h : arithmeticInitialInfinityCompatible hπ data H m k hk f) :
    C (.initial false) (.initial true) := by
  dsimp only
  have T := arithmeticLabeledAtlas_initial_isPullback hπ data H m k hk
  apply (cancel_epi T.isoPullback.hom).mp
  simpa only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd] using h.1.symm.trans h.2

/-- The explicit infinity equations are equivalent to both full labeled compatibility tests. -/
theorem arithmeticInitialInfinity_compatible_iff :
    arithmeticInitialInfinityCompatible hπ data H m k hk f ↔
      C .infinity (.initial false) ∧ C .infinity (.initial true) := by
  rw [arithmeticInitialInfinity_first_iff, arithmeticInitialInfinity_opposite_iff]
  rfl

end FLT.Mazur.WeierstrassDividedDepth

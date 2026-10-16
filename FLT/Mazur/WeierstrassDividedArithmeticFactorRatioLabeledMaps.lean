/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioAtlasOverlap
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAtlasRestriction

/-!
# Full corrected polygon maps on the original initial and infinity atlas labels

The original factor identities supply the infinity coefficient hypotheses.
Both initial labels use the complete affine map and retain its quotient square.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFactorRatioTensorAffineMap arithmeticFactorRatioTensorInfinityMap
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))

include data H in
/-- The original third coefficient is divisible by the arithmetic parameter. -/
theorem ArithmeticAtlasCoefficients.a3_div : π ∣ W.a₃ := by
  rw [Data.factor3 d]
  exact dvd_mul_of_dvd_right (H.b3_div _) _

include data H in
/-- The original fourth coefficient is divisible by the same parameter. -/
theorem ArithmeticAtlasCoefficients.a4_div : π ∣ W.a₄ := by
  rw [Data.factor4 d]
  exact dvd_mul_of_dvd_right (H.b4_div _) _

include data H in
/-- The original sixth coefficient retains its full squared scale and divisibility. -/
theorem ArithmeticAtlasCoefficients.a6_div : π ∣ W.a₆ := by
  rw [Data.factor6 d]
  exact dvd_mul_of_dvd_right (H.b6_div _) _

variable [IsDomain R] [IsBezout R] (hπ : π ≠ 0) (m k : ℕ) (hk : k ≤ n)
local notation "Y" => arithmeticFactorRatioPolygon π m W (π ^ start) H.a1_unit H.scale_div k
local notation "A" => arithmeticFactorRatioTensorAffineMap π m W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- The full initial labeled atlas comparison, with both original tangent roots. -/
def arithmeticFactorRatioLabeledInitialMap (b : Bool) :
    arithmeticLabeledAtlasObject hπ data H m k hk (.initial b) ⟶ Y :=
  (if b then arithmeticOppositeInitialTensorNodeChart π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)
    else arithmeticInitialTensorNodeChart π m W (π ^ start)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
        (H.b3_div _) (H.b4_div _) (H.b6_div _)) ≫ A k

/-- The entire original infinity label has the regular full factor-ratio comparison. -/
def arithmeticFactorRatioLabeledInfinityMap :
    arithmeticLabeledAtlasObject hπ data H m k hk .infinity ⟶ Y :=
  arithmeticFactorRatioTensorInfinityMap π m W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)
      (H.a3_div data) (H.a4_div data) (H.a6_div data) k

omit [IsBezout R] in
/-- Both original initial atlas labels commute with the complete arithmetic quotient square. -/
@[reassoc] theorem arithmeticFactorRatioLabeledInitialMap_restriction (b : Bool) :
    arithmeticFactorRatioLabeledInitialMap data H hπ m k hk b ≫
      arithmeticFactorRatioPolygonRestriction π m W (π ^ start) H.a1_unit H.scale_div k =
      arithmeticLabeledAtlasRestriction hπ data H m k hk (.initial b) ≫
        arithmeticFactorRatioLabeledInitialMap data H hπ (m + 1) k hk b := by
  unfold arithmeticFactorRatioLabeledInitialMap
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [Category.assoc, arithmeticFactorRatioTensorAffineMap_restriction,
      ← arithmeticInitialTensorNodeChart_restriction_assoc]
    rfl
  · rw [Category.assoc, arithmeticFactorRatioTensorAffineMap_restriction,
      ← arithmeticOppositeInitialTensorNodeChart_restriction_assoc]
    rfl

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAtlas
public import FLT.Mazur.WeierstrassDividedArithmeticTensorRestriction
public import FLT.Mazur.WeierstrassSuccessiveArithmeticTensorRestrictionSquare
public import FLT.Mazur.WeierstrassDilatationArithmeticTensorNormalization

/-!
# Fixed-stage quotient squares for every retained label and the terminal node

Both labels at every retained depth and the complete normalized terminal node
commute with the original global arithmetic restriction at the same fixed stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX WeierstrassDilatation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n)
local notation "d" => data (Fin.mk k (Nat.lt_succ_of_le hk))
local notation "c₀" => arithmeticTerminalSmoothing π m W (π ^ (start + k))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale k) H.a2_div
    (H.b4_div _) (H.b6_div _)
local notation "c₁" => arithmeticTerminalSmoothing π (m + 1) W (π ^ (start + k))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale k) H.a2_div
    (H.b4_div _) (H.b6_div _)

/-- The actual coefficient restriction of the full normalized terminal node. -/
def arithmeticLabeledTerminalRestriction :
    arithmeticLabeledAtlasObject hπ data H m k hk .terminal ⟶
      arithmeticLabeledAtlasObject hπ data H (m + 1) k hk .terminal :=
  Spec.map (CommRingCat.ofHom (NodalFiber.coefficientRingMap
    (AlgHom.toRingHom (restriction R π m)) c₁ c₀
      (arithmeticTerminalSmoothing_restriction R π m W (π ^ (start + k))
        (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale k) H.a2_div
          (H.b4_div _) (H.b6_div _))))

/-- The full terminal node square uses the original global quotient map. -/
@[reassoc] theorem arithmeticLabeledTerminalChart_restriction :
    arithmeticLabeledTerminalRestriction hπ data H m k hk ≫
      arithmeticLabeledTerminalChart hπ data H (m + 1) k hk =
        arithmeticLabeledTerminalChart hπ data H m k hk ≫
          finiteGlobalArithmeticRestriction hπ data k hk m := by
  unfold arithmeticLabeledTerminalChart arithmeticLabeledTerminalRestriction
  rw [← Category.assoc, arithmeticTerminalNodeIso_restriction, Category.assoc]
  change _ ≫ TensorCoefficientMap.spectrum (restriction R π m) ≫ _ = _
  rw [finiteArithmeticDividedTensorChart_restriction, Category.assoc]

/-- Every retained depth and both labels commute at their fixed containing stage. -/
@[reassoc] theorem arithmeticLabeledRetainedChart_restriction (a : Fin k) (opposite : Bool) :
    arithmeticPolygonNodeRestriction R π m ≫
      arithmeticLabeledRetainedChart hπ data H (m + 1) k hk a opposite =
        arithmeticLabeledRetainedChart hπ data H m k hk a opposite ≫
          finiteGlobalArithmeticRestriction hπ data k hk m := by
  unfold arithmeticLabeledRetainedChart
  rw [← Category.assoc, arithmeticTensorBranchChart_restriction, Category.assoc,
    arithmeticRetainedTensorChart_restriction, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth

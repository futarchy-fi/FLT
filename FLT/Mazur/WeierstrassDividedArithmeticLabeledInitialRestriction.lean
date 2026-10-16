/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledNodeRestriction
public import FLT.Mazur.WeierstrassModificationXArithmeticTensorRestrictionSquare

/-!
# Both full initial labels commute with the original global quotient

At every fixed containing stage, both full initial neighborhoods have the
actual coefficient quotient square with the unchanged global arithmetic model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n)

/-- Both full initial labels retain the actual global quotient at their fixed stage. -/
@[reassoc] theorem arithmeticLabeledInitialChart_restriction (opposite : Bool) :
    arithmeticInitialNodeRestriction R π m W (π ^ start) ≫
      arithmeticLabeledInitialChart hπ data H (m + 1) k hk opposite =
        arithmeticLabeledInitialChart hπ data H m k hk opposite ≫
          finiteGlobalArithmeticRestriction hπ data k hk m := by
  cases opposite
  · simp only [arithmeticLabeledInitialChart, Bool.false_eq_true, ↓reduceIte]
    rw [← Category.assoc, arithmeticInitialTensorNodeChart_restriction,
      Category.assoc, finiteArithmeticInitialTensorChart_restriction, Category.assoc]
  · simp only [arithmeticLabeledInitialChart, ↓reduceIte]
    rw [← Category.assoc, arithmeticOppositeInitialTensorNodeChart_restriction,
      Category.assoc, finiteArithmeticInitialTensorChart_restriction, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth

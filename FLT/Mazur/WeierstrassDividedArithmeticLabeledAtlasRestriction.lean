/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledInitialRestriction

/-!
# The complete labeled arithmetic quotient diagram

Every original chart has its coefficient restriction: infinity, the full
terminal node, both full initial nodes, and both labels at each retained depth.
All squares use the same fixed containing stage and actual global quotient.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n)

/-- The original quotient restrictions on every label of the complete arithmetic atlas. -/
def arithmeticLabeledAtlasRestriction (i : ArithmeticChartLabel k) :
    arithmeticLabeledAtlasObject hπ data H m k hk i ⟶
      arithmeticLabeledAtlasObject hπ data H (m + 1) k hk i :=
  match i with
  | .infinity => TensorCoefficientMap.spectrum (restriction R π m)
  | .terminal => arithmeticLabeledTerminalRestriction hπ data H m k hk
  | .initial _ => arithmeticInitialNodeRestriction R π m W (π ^ start)
  | .retained _ _ => arithmeticPolygonNodeRestriction R π m

/-- The entire labeled atlas commutes with the actual global arithmetic quotient. -/
@[reassoc] theorem arithmeticLabeledAtlasMap_restriction (i : ArithmeticChartLabel k) :
    arithmeticLabeledAtlasRestriction hπ data H m k hk i ≫
      arithmeticLabeledAtlasMap hπ data H (m + 1) k hk i =
        arithmeticLabeledAtlasMap hπ data H m k hk i ≫
          finiteGlobalArithmeticRestriction hπ data k hk m := by
  cases i with
  | infinity => exact arithmeticTensorAtlas_infinity_restriction hπ data m k hk
  | terminal => exact arithmeticLabeledTerminalChart_restriction hπ data H m k hk
  | initial b => exact arithmeticLabeledInitialChart_restriction hπ data H m k hk b
  | retained a b => exact arithmeticLabeledRetainedChart_restriction hπ data H m k hk a b

end FLT.Mazur.WeierstrassDividedDepth

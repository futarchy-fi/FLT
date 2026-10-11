/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartUnitLift
public import FLT.Mazur.WeierstrassLeftSmoothFiveAffineTriple
public import Mathlib.Algebra.Regular.Pow

/-!
# The five points used in whole-cubic action associativity descent

Select the three original inputs and the two actual inner sums as morphisms
to the projective curve, retaining their compatibility with every source change.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The three actual original inputs followed by the two actual inner sums. -/
def leftSmoothTripleFivePoint {X : Scheme.{u}} (t : X ⟶ leftSmoothTriple W) :
    Fin 5 → (X ⟶ integralCurve W) :=
  ![t ≫ leftSmoothTripleFirst W ≫ (integralSmoothOpen W).ι,
    t ≫ leftSmoothTripleSecond W ≫ (integralSmoothOpen W).ι,
    t ≫ leftSmoothTripleThird W,
    t ≫ leftSmoothTriplePair W ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι,
    t ≫ leftSmoothTripleLastPair W ≫ leftSmoothFactorAddition W]

/-- The five selected points commute with changing the source. -/
theorem leftSmoothTripleFivePoint_comp {X Y : Scheme.{u}} (t : X ⟶ leftSmoothTriple W)
    (f : Y ⟶ X) (i : Fin 5) :
    leftSmoothTripleFivePoint W (f ≫ t) i = f ≫ leftSmoothTripleFivePoint W t i := by
  fin_cases i <;> simp [leftSmoothTripleFivePoint, Category.assoc]

end FLT.Mazur.WeierstrassIntegralChart

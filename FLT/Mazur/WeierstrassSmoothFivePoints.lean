/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartUnitLift
public import FLT.Mazur.WeierstrassSmoothFiveAffineTriple
public import Mathlib.Algebra.Regular.Pow

/-!
# The five points used in smooth associativity descent

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
def smoothTripleFivePoint {X : Scheme.{u}} (t : X ⟶ smoothFactorTriple W) :
    Fin 5 → (X ⟶ integralCurve W) :=
  ![t ≫ smoothFactorTripleFirst W ≫ (integralSmoothOpen W).ι,
    t ≫ smoothFactorTripleSecond W ≫ (integralSmoothOpen W).ι,
    t ≫ smoothFactorTripleThird W ≫ (integralSmoothOpen W).ι,
    t ≫ smoothFactorTriplePair W ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι,
    t ≫ smoothFactorTripleLastPair W ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι]

/-- The five selected points commute with changing the source. -/
theorem smoothTripleFivePoint_comp {X Y : Scheme.{u}} (t : X ⟶ smoothFactorTriple W)
    (f : Y ⟶ X) (i : Fin 5) :
    smoothTripleFivePoint W (f ≫ t) i = f ≫ smoothTripleFivePoint W t i := by
  fin_cases i <;> simp [smoothTripleFivePoint, Category.assoc]

end FLT.Mazur.WeierstrassIntegralChart

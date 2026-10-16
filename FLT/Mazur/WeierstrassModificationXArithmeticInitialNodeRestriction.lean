/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXCanonicalNodeCoefficientTransport
public import FLT.Mazur.WeierstrassModificationXArithmeticRestrictionMaps
public import FLT.Mazur.WeierstrassModificationXArithmeticInitialCover

/-!
# Both complete initial node squares under arithmetic restriction

The original small and opposite charts commute with the actual quotient maps
on the whole neighborhoods. Each order uses its independently constructed root.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π : R) (m : ℕ)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (ha : IsUnit W.a₁) (h2 : π ∣ W.a₂) (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6)

attribute [local irreducible] polynomialSlopeRoot polynomialNodeChart polynomialOppositeNodeChart

/-- The complete first initial node chart follows the actual quotient restriction. -/
@[reassoc] theorem arithmeticInitialNodeChart_restriction :
    arithmeticFullInitialNodeQuotient R π m W s ≫
      arithmeticInitialNodeChart π (m + 1) W s b3 b4 b6 ha h2 h3 h4 h6 =
        arithmeticInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6 ≫
          arithmeticInitialRestriction R π m W s b3 b4 b6 := by
  unfold arithmeticFullInitialNodeQuotient arithmeticInitialNodeChart
    arithmeticInitialRestriction arithmeticInitialCoefficientRingMap
  apply canonicalPolynomialNodeChart_coefficient_of_eq
  exact arithmeticParameterIdeal_restriction R π m

/-- The complete opposite initial chart follows the same actual quotient restriction. -/
@[reassoc] theorem arithmeticOppositeInitialNodeChart_restriction :
    arithmeticFullInitialNodeQuotient R π m W s ≫
      arithmeticOppositeInitialNodeChart π (m + 1) W s b3 b4 b6 ha h2 h3 h4 h6 =
        arithmeticOppositeInitialNodeChart π m W s b3 b4 b6 ha h2 h3 h4 h6 ≫
          arithmeticInitialRestriction R π m W s b3 b4 b6 := by
  unfold arithmeticFullInitialNodeQuotient arithmeticOppositeInitialNodeChart
    arithmeticInitialRestriction arithmeticInitialCoefficientRingMap
  apply canonicalPolynomialOppositeNodeChart_coefficient_of_eq
  exact arithmeticParameterIdeal_restriction R π m

end FLT.Mazur.WeierstrassModificationX

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LocalizationFixedInvolution
public import FLT.Mazur.WeierstrassDilatationNegationContraction
public import FLT.Mazur.WeierstrassDilatationHorizontalCongruence

/-!
# The actual horizontal boundary is invariant under divided negation

Construct its involution by localizing the divided inverse at the fixed
horizontal coordinate. Parameter comparisons preserve both constructed maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- Negation of the entire actual horizontal boundary. -/
def horizontalNegationIso : Spec (.of (HorizontalCoordinate W s b3 b4 b6)) ≅
    Spec (.of (HorizontalCoordinate W s b3 b4 b6)) :=
  LocalizationFixedInvolution.specIso (negation W s b3 b4 b6) (x W s b3 b4 b6)
    (negation_x W s b3 b4 b6) (negation_comp W s b3 b4 b6)

/-- Boundary negation retains the exact principal-open inclusion. -/
@[reassoc] theorem horizontalNegationIso_inclusion :
    (horizontalNegationIso W s b3 b4 b6).hom ≫ horizontalInclusion W s b3 b4 b6 =
      horizontalInclusion W s b3 b4 b6 ≫ (negationIso W s b3 b4 b6).hom :=
  LocalizationFixedInvolution.specIso_inclusion (negation W s b3 b4 b6) (x W s b3 b4 b6)
    (negation_x W s b3 b4 b6) (negation_comp W s b3 b4 b6)

/-- Boundary negation is its own inverse as an actual morphism. -/
theorem horizontalNegationIso_inv : (horizontalNegationIso W s b3 b4 b6).inv =
    (horizontalNegationIso W s b3 b4 b6).hom := rfl

/-- Divided negation is retained by the actual parameter-identification map. -/
@[reassoc] theorem negationIso_parameter (t c3 c4 c6 : R)
    (hs : s = t) (h3 : b3 = c3) (h4 : b4 = c4) (h6 : b6 = c6) :
    (negationIso W t c3 c4 c6).hom ≫
        (parameterSpecIso W s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6).hom =
      (parameterSpecIso W s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6).hom ≫
        (negationIso W s b3 b4 b6).hom := by
  subst t c3 c4 c6
  simp [parameterSpecIso, parameterEquiv]

/-- The same parameter-identification retains the actual boundary negative. -/
@[reassoc] theorem horizontalNegationIso_parameter (t c3 c4 c6 : R)
    (hs : s = t) (h3 : b3 = c3) (h4 : b4 = c4) (h6 : b6 = c6) :
    (horizontalNegationIso W t c3 c4 c6).hom ≫
        (horizontalParameterIso W s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6).hom =
      (horizontalParameterIso W s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6).hom ≫
        (horizontalNegationIso W s b3 b4 b6).hom := by
  subst t c3 c4 c6
  simp [horizontalParameterIso, horizontalParameterEquiv]

end FLT.Mazur.WeierstrassDilatation

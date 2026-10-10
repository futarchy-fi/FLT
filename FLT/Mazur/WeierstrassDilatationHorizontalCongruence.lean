/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationParameterCongruence
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Parameter congruence on the divided horizontal opens

The horizontal open and its inclusion are transported by the same actual
parameter equality as the divided coordinate algebra. This supplies the
boundary identification needed to repeat chart replacement at named depths.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The actual horizontal principal open of any divided chart. -/
abbrev HorizontalCoordinate (s b3 b4 b6 : R) := Localization.Away (x W s b3 b4 b6)

/-- The inclusion of that principal open in its divided chart. -/
def horizontalInclusion (s b3 b4 b6 : R) :
    Spec (.of (HorizontalCoordinate W s b3 b4 b6)) ⟶ Spec (.of (Coordinate W s b3 b4 b6)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Coordinate W s b3 b4 b6) _))

instance horizontalInclusion_isOpenImmersion (s b3 b4 b6 : R) :
    IsOpenImmersion (horizontalInclusion W s b3 b4 b6) :=
  IsOpenImmersion.of_isLocalization (x W s b3 b4 b6)

variable (s t b3 b4 b6 c3 c4 c6 : R)
  (hs : s = t) (h3 : b3 = c3) (h4 : b4 = c4) (h6 : b6 = c6)

/-- The contravariant scheme identification of equal divided parameters. -/
def parameterSpecIso : Spec (.of (Coordinate W t c3 c4 c6)) ≅
    Spec (.of (Coordinate W s b3 b4 b6)) :=
  Scheme.Spec.mapIso
    (parameterEquiv W s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6).toRingEquiv.toCommRingCatIso.op

/-- The same parameter equality identifies the actual localized algebras. -/
def horizontalParameterEquiv : HorizontalCoordinate W s b3 b4 b6 ≃ₐ[R]
    HorizontalCoordinate W t c3 c4 c6 := by
  subst t c3 c4 c6
  exact AlgEquiv.refl

/-- The horizontal boundary identification induced by the localized equality. -/
def horizontalParameterIso : Spec (.of (HorizontalCoordinate W t c3 c4 c6)) ≅
    Spec (.of (HorizontalCoordinate W s b3 b4 b6)) :=
  Scheme.Spec.mapIso
    (horizontalParameterEquiv W s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6).toRingEquiv.toCommRingCatIso.op

/-- The boundary transport commutes with its actual open inclusion. -/
@[reassoc] theorem horizontalParameterIso_inclusion :
    (horizontalParameterIso W s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6).hom ≫
        horizontalInclusion W s b3 b4 b6 =
      horizontalInclusion W t c3 c4 c6 ≫
        (parameterSpecIso W s t b3 b4 b6 c3 c4 c6 hs h3 h4 h6).hom := by
  subst t c3 c4 c6
  simp [horizontalParameterIso, horizontalParameterEquiv, parameterSpecIso, parameterEquiv]

end FLT.Mazur.WeierstrassDilatation

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalLocalizationSquare

/-!
# Principal restriction with a named target coordinate

The target coordinate can be named independently of its defining image.
The resulting restriction retains every original function and the exact
principal-open pullback square.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PrincipalLocalizationNamedSquare
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
  (f : A →+* B) (x : A) (y : B) (h : f x = y)

/-- Restrict the original ring map to the two named principal localizations. -/
def ringMap : Localization.Away x →+* Localization.Away y := by
  subst y
  exact IsLocalization.Away.map _ _ f x

/-- The localized comparison keeps the original map on every function. -/
theorem ringMap_algebraMap (a : A) :
    ringMap f x y h (algebraMap A _ a) = algebraMap B _ (f a) := by
  subst y
  simp [ringMap, IsLocalization.Away.map]

/-- The restriction of the original spectrum map to the named opens. -/
def boundaryMap : Spec (.of (Localization.Away y)) ⟶
    Spec (.of (Localization.Away x)) :=
  Spec.map (CommRingCat.ofHom (ringMap f x y h))

/-- The named principal opens form the exact inverse-image square. -/
theorem isPullback :
    IsPullback (boundaryMap f x y h) (PrincipalLocalizationSquare.inclusion y)
      (PrincipalLocalizationSquare.inclusion x) (Spec.map (CommRingCat.ofHom f)) := by
  subst y
  exact PrincipalLocalizationSquare.isPullback f x

/-- The whole boundary comparison commutes with both original inclusions. -/
@[reassoc] theorem boundaryMap_inclusion :
    boundaryMap f x y h ≫ PrincipalLocalizationSquare.inclusion x =
      PrincipalLocalizationSquare.inclusion y ≫ Spec.map (CommRingCat.ofHom f) :=
  (isPullback f x y h).w

end FLT.Mazur.PrincipalLocalizationNamedSquare

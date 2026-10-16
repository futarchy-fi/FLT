/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Two original maps on a common principal neighborhood

Invert the product of the two images of the same denominator. Both maps
then extend from the original localization, retaining their values exactly.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PairedAwayLocalization
variable {A B : Type*} [CommRing A] [CommRing B] (f g : A →+* B) (d : A)

/-- The common neighborhood in the unchanged receiving ring. -/
abbrev Ring := Localization.Away (f d * g d)

/-- The first denominator is a unit on the common neighborhood. -/
theorem first_isUnit : IsUnit (algebraMap B (Ring f g d) (f d)) :=
  IsLocalization.Away.isUnit_of_dvd (f d * g d) (dvd_mul_right _ _)

/-- The second denominator is a unit on that same neighborhood. -/
theorem second_isUnit : IsUnit (algebraMap B (Ring f g d) (g d)) :=
  IsLocalization.Away.isUnit_of_dvd (f d * g d) (dvd_mul_left _ _)

/-- Extension of the first actual map, without changing the source localization. -/
def first : Localization.Away d →+* Ring f g d :=
  IsLocalization.Away.lift d (g := (algebraMap B (Ring f g d)).comp f)
    (first_isUnit f g d)

/-- Extension of the second actual map into precisely the same ring. -/
def second : Localization.Away d →+* Ring f g d :=
  IsLocalization.Away.lift d (g := (algebraMap B (Ring f g d)).comp g)
    (second_isUnit f g d)

/-- The first extended map retains every original element. -/
theorem first_algebraMap (z : A) :
    first f g d (algebraMap A (Localization.Away d) z) =
      algebraMap B (Ring f g d) (f z) := IsLocalization.Away.lift_eq _ _ _

/-- The second extended map retains every original element. -/
theorem second_algebraMap (z : A) :
    second f g d (algebraMap A (Localization.Away d) z) =
      algebraMap B (Ring f g d) (g z) := IsLocalization.Away.lift_eq _ _ _

end FLT.Mazur.PairedAwayLocalization

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-! # Transport principal-neighbourhood ideal equality along any map -/

@[expose] public noncomputable section

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S]

/-- An ideal equality on a principal open persists under any ring map on which
its denominator becomes a unit. -/
theorem map_eq_of_isUnit_of_away_eq (I J : Ideal R) (a : R)
    (h : I.map (algebraMap R (Localization.Away a)) =
      J.map (algebraMap R (Localization.Away a))) (f : R →+* S) (ha : IsUnit (f a)) :
    I.map f = J.map f := by
  let := f.toAlgebra
  let g : Localization.Away a →+* S := IsLocalization.Away.lift a ha
  have hg : g.comp (algebraMap R (Localization.Away a)) = f := by
    apply RingHom.ext
    intro r
    exact IsLocalization.Away.lift_eq a ha r
  simpa only [Ideal.map_map, hg] using congrArg (Ideal.map g) h

end Ideal

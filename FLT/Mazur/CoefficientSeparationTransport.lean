/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCoefficientDifferenceIdeal

/-!
# Original coefficient separation on arbitrary scalar tests

Mapping the full coefficient difference ideal gives the difference ideal of
the mapped coordinates. Consequently geometric separation survives every
scalar map, including all correction quotients and nonreduced tests.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteCoefficientDifference
variable {A T U : Type*} [CommRing A] [CommRing T] [CommRing U]
  (l r : A →+* T) (g : T →+* U)

/-- Full coefficient difference ideals commute with arbitrary scalar maps. -/
theorem map_differenceIdeal :
    Ideal.map g (differenceIdeal l r) = differenceIdeal (g.comp l) (g.comp r) := by
  simp only [differenceIdeal, Ideal.map_span, ← Set.range_comp, Function.comp_def,
    map_sub, RingHom.comp_apply]

/-- Separation persists on any scalar test, including a correction quotient. -/
theorem differenceIdeal_comp_eq_top (h : differenceIdeal l r = ⊤) :
    differenceIdeal (g.comp l) (g.comp r) = ⊤ := by
  rw [← map_differenceIdeal, h, Ideal.map_top]

end FLT.Mazur.FiniteCoefficientDifference

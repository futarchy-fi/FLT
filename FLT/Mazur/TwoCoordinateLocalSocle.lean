/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Detect a full coordinate socle using only local rings at the node

Away from either coordinate, its unit image kills a common annihilator.
At the node, it suffices to kill generators of an ideal containing it.
All tests take place in full localizations, rather than residue fields.
-/

public section
namespace FLT.Mazur.TwoCoordinateLocalSocle
variable {R : Type*} [CommRing R]

/-- Local vanishing of an ideal at node primes kills its full coordinate socle. -/
theorem eq_zero (I : Ideal R) (x y z : R) (hz : z ∈ I)
    (hx : x * z = 0) (hy : y * z = 0)
    (hl : ∀ p : PrimeSpectrum R, x ∈ p.asIdeal → y ∈ p.asIdeal →
      ∀ a ∈ I, algebraMap R (Localization.AtPrime p.asIdeal) a = 0) : z = 0 := by
  apply eq_zero_of_localization
  intro P hP
  by_cases hxp : x ∈ P
  · by_cases hyp : y ∈ P
    · exact hl ⟨P, inferInstance⟩ hxp hyp z hz
    · have hu : IsUnit (algebraMap R (Localization.AtPrime P) y) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff _ P y).mpr hyp
      apply hu.mul_right_eq_zero.mp
      rw [← map_mul, hy, map_zero]
  · have hu : IsUnit (algebraMap R (Localization.AtPrime P) x) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ P x).mpr hxp
    apply hu.mul_right_eq_zero.mp
    rw [← map_mul, hx, map_zero]

end FLT.Mazur.TwoCoordinateLocalSocle

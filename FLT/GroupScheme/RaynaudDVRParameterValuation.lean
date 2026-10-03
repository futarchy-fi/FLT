/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Data.ENat.SuccOrder

/-!
# Raynaud parameter digits over an arbitrary discrete valuation ring

The product of two parameters equal to a uniformizer times a unit has
complementary binary valuations. The unit/uniformizer alternatives are intrinsic
to the DVR; choosing presentations and proving that p remains a uniformizer
under unramified base change are separate constructions.
-/

@[expose] public section

namespace RaynaudParameters

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The parameter product has additive valuation one over any DVR. -/
theorem dvr_valuation_pair {π a b : R} (hπ : Irreducible π) (u : Rˣ)
    (h : a * b = π * u) : addVal R a + addVal R b = 1 := by
  have hv := congrArg (addVal R) h
  simpa only [addVal_mul, addVal_uniformizer hπ, addVal_eq_zero_of_unit, add_zero] using hv

/-- The two parameter valuations are complementary binary digits. -/
theorem dvr_valuation_digits {π a b : R} (hπ : Irreducible π) (u : Rˣ)
    (h : a * b = π * u) :
    (addVal R a = 0 ∧ addVal R b = 1) ∨
      (addVal R a = 1 ∧ addVal R b = 0) := by
  have hv := dvr_valuation_pair hπ u h
  have ha : addVal R a ≤ 1 := le_self_add.trans_eq hv
  have hb : addVal R b ≤ 1 := le_add_self.trans_eq hv
  rcases Order.le_one_iff.mp ha with ha | ha <;>
    rcases Order.le_one_iff.mp hb with hb | hb <;> simp_all

/-- Exactly one parameter is a unit and the other is associated to the uniformizer. -/
theorem dvr_unit_or_uniformizer {π a b : R} (hπ : Irreducible π) (u : Rˣ)
    (h : a * b = π * u) :
    (IsUnit a ∧ Associated b π) ∨ (Associated a π ∧ IsUnit b) := by
  simpa only [← addVal_eq_zero_iff, ← addVal_eq_iff_associated,
    addVal_uniformizer hπ] using dvr_valuation_digits hπ u h

end RaynaudParameters

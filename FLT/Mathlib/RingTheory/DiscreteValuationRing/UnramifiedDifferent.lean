/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.DiscreteValuationRing.UniformizerDifferentBound
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic

/-!
# The different of an unramified coefficient DVR

A base uniformizer remaining irreducible forces ramification index one.
With finite residue field, the different is the unit ideal.
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing

namespace IsDiscreteValuationRing

variable {R C : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero R] [Finite (ResidueField R)]
  [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra R C]
  [Module.Finite R C] [FaithfulSMul R C]

attribute [local instance] FractionRing.liftAlgebra

/-- If a uniformizer remains a uniformizer, the different is the unit ideal. -/
theorem differentIdeal_eq_top_of_map_uniformizer {π : R} (hπ : Irreducible π)
    (hπC : Irreducible (algebraMap R C π)) : differentIdeal R C = ⊤ := by
  have : CharZero C := Algebra.charZero_of_charZero R C
  have : Finite (R ⧸ maximalIdeal R) := inferInstanceAs (Finite (ResidueField R))
  have : Finite (maximalIdeal R).ResidueField := inferInstance
  have : PerfectField (maximalIdeal R).ResidueField := inferInstance
  have : Algebra.HasSeparableResidueFieldsAt R C ((maximalIdeal C).under R) := by
    simpa only [Ideal.under_def, maximalIdeal_comap] using
      (inferInstance : Algebra.HasSeparableResidueFieldsAt R C (maximalIdeal R))
  have he : (maximalIdeal C).ramificationIdx R = 1 := by
    have hv := addValMapUniformizerEqRamificationIdx (S := C) hπ
    rw [addVal_uniformizer hπC] at hv
    exact_mod_cast hv.symm
  have huc : Algebra.IsUnramifiedAt R (maximalIdeal C) :=
    Ideal.ramificationIdx_eq_one_iff.mp he
  by_contra hne
  exact (not_dvd_differentIdeal_iff.mpr huc)
    (Ideal.dvd_iff_le.mpr (le_maximalIdeal hne))

end IsDiscreteValuationRing

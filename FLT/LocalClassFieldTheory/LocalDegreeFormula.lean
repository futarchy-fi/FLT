/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedDegree
public import Mathlib.NumberTheory.RamificationInertia.Ramification

/-!
# The local degree as ramification times residue degree

The local fundamental identity is expressed with the ramification index
used by normalized order and the actual residue-field degree.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing

variable (R S K L : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The degree of a finite DVR fraction extension is e times f. -/
theorem localDegree_eq_ramification_mul_residue :
    (maximalIdeal R).ramificationIdx' (maximalIdeal S) *
      Module.finrank (ResidueField R) (ResidueField S) = Module.finrank K L := by
  let : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  let : IsIntegralClosure S R L := IsIntegralClosure.of_isIntegrallyClosed S R L
  have h := Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing S
    (IsDiscreteValuationRing.not_a_field R)
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (IsDiscreteValuationRing.not_a_field R)]
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal R), IsIntegralClosure.rank R K L S] at h
  exact h

end LocalClassFieldTheory

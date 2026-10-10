/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisOpenInvariance
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Residue-field detection of the prescribed basis open

The prime-local basis condition equals the basis condition in the actual
residue-field fiber. No reducedness assumption on the base ring is needed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

variable {S A : Type*} [CommRing S] [CommRing A] [Algebra S A] {d : ℕ}
variable (b : Module.Basis (Fin d) S A) (y : Fin d → A)

/-- Membership is detected by the actual proposed basis in the residue-field fiber. -/
theorem mem_basisOpen_iff_residueField (p : PrimeSpectrum S) :
    p ∈ basisOpen b y ↔
      ∃ c : Module.Basis (Fin d) p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[S] A),
        ∀ i, c i = baseChangedTuple y p.asIdeal.ResidueField i := by
  rw [baseChange_exists_basis_iff b y, isUnit_iff_ne_zero,
    ne_eq, Ideal.algebraMap_residueField_eq_zero]
  rfl

include b in
/-- For a finite free family, the residue-field basis lifts to the prime localization. -/
theorem primeLocal_basis_iff_residueField (p : PrimeSpectrum S) :
    (∃ c : Module.Basis (Fin d) (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[S] A),
      ∀ i, c i = baseChangedTuple y (Localization.AtPrime p.asIdeal) i) ↔
    ∃ c : Module.Basis (Fin d) p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[S] A),
      ∀ i, c i = baseChangedTuple y p.asIdeal.ResidueField i := by
  rw [← mem_basisOpen_iff b y, mem_basisOpen_iff_residueField]

/-- Every point of the open has a canonical principal neighborhood carrying the given basis. -/
theorem basis_on_determinant_localization :
    ∃ c : Module.Basis (Fin d) (Localization.Away (basisDeterminant b y))
      (Localization.Away (basisDeterminant b y) ⊗[S] A),
      ∀ i, c i = baseChangedTuple y (Localization.Away (basisDeterminant b y)) i := by
  rw [baseChange_exists_basis_iff b y]
  exact IsLocalization.Away.algebraMap_isUnit (basisDeterminant b y)

end FLT.Mazur.HilbertChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIntrinsicBasisOpen
public import FLT.Mazur.HilbertLocalResidueBasis
public import FLT.Mazur.HilbertTupleBasisTower

/-!
# Residue-field detection for the intrinsic basis open

Finite presentation makes the prime-local basis locus open. Flatness allows
its membership to be tested in the residue fiber, without a global basis.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.FinitePresentation R M] [Module.Flat R M] {d : ℕ}

/-- The intrinsic basis open of a finite flat family is detected by residue-field bases. -/
theorem mem_intrinsicBasisOpen_iff_residueField (y : Fin d → M) (p : PrimeSpectrum R) :
    p ∈ intrinsicBasisOpen y ↔
      ∃ b : Module.Basis (Fin d) p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M),
        ∀ i, b i = (1 : p.asIdeal.ResidueField) ⊗ₜ[R] y i := by
  rw [mem_intrinsicBasisOpen_iff, local_basis_iff_residue_basis]
  exact tuple_basis_tower_iff (S := Localization.AtPrime p.asIdeal) y

/-- A residue basis extends to a principal neighborhood with the same prescribed vectors. -/
theorem exists_principal_basis_neighborhood_of_residue (y : Fin d → M)
    (p : PrimeSpectrum R)
    (b : Module.Basis (Fin d) p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M))
    (hb : ∀ i, b i = (1 : p.asIdeal.ResidueField) ⊗ₜ[R] y i) :
    ∃ r : R, r ∉ p.asIdeal ∧
      (∃ c : Module.Basis (Fin d) (Localization.Away r) (Localization.Away r ⊗[R] M),
        ∀ i, c i = (1 : Localization.Away r) ⊗ₜ[R] y i) ∧
      PrimeSpectrum.basicOpen r ≤ intrinsicBasisOpen y := by
  exact exists_principal_basis_neighborhood y p
    ((mem_intrinsicBasisOpen_iff_residueField y p).mpr ⟨b, hb⟩)

end FLT.Mazur.HilbertChart

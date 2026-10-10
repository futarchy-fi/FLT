/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIntrinsicResidueBasis
public import FLT.Mazur.HilbertFaithfullyFlatTupleBasis

/-!
# Arbitrary base change of the intrinsic basis open

Residue fields at a point and its image are related by a field extension.
Faithfully flat detection and tensor cancellation therefore identify the
actual intrinsic opens for every base change of a finitely presented flat module.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.FinitePresentation R M] [Module.Flat R M] {d : ℕ}
variable (S : Type*) [CommRing S] [Algebra R S]

/-- The intrinsic basis open commutes with every scalar extension of a finite flat family. -/
theorem intrinsicBasisOpen_baseChange (y : Fin d → M) :
    intrinsicBasisOpen (fun i ↦ (1 : S) ⊗ₜ[R] y i) =
      TopologicalSpace.Opens.comap
        ⟨PrimeSpectrum.comap (algebraMap R S), PrimeSpectrum.continuous_comap _⟩
        (intrinsicBasisOpen y) := by
  ext q
  let p := PrimeSpectrum.comap (algebraMap R S) q
  let _ : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S) rfl).toAlgebra
  let _ : IsScalarTower R p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R q.asIdeal.ResidueField r =
        Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R S) rfl
          (algebraMap R p.asIdeal.ResidueField r)
      exact (IsScalarTower.algebraMap_apply R S q.asIdeal.ResidueField r).trans
        (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal (algebraMap R S) rfl r).symm
  change q ∈ intrinsicBasisOpen (fun i ↦ (1 : S) ⊗ₜ[R] y i) ↔ p ∈ intrinsicBasisOpen y
  rw [mem_intrinsicBasisOpen_iff_residueField, mem_intrinsicBasisOpen_iff_residueField,
    tuple_basis_tower_iff]
  rw [tuple_basis_iff_faithfullyFlat (R := p.asIdeal.ResidueField)
    q.asIdeal.ResidueField]
  exact (tuple_basis_tower_iff (S := p.asIdeal.ResidueField) y).symm

end FLT.Mazur.HilbertChart

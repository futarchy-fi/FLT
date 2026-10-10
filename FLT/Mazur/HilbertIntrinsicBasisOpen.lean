/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertLocalizedTupleBasis
public import FLT.Mazur.HilbertBasisOpenInvariance

/-!
# The prescribed basis open without a global trivialization

For any finitely presented module, the prime-local basis locus is an actual
open subset. It agrees with the determinant open whenever a basis is available,
and every point has a principal neighborhood carrying the prescribed basis.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

attribute [local irreducible] tupleLinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable [Module.FinitePresentation R M] {d : ℕ}

/-- The actual open locus where a tuple trivializes a finitely presented module. -/
def intrinsicBasisOpen (y : Fin d → M) : TopologicalSpace.Opens (PrimeSpectrum R) :=
  ⟨localIsomorphismLocus (tupleLinearMap y), isOpen_localIsomorphismLocus _⟩

/-- Membership means that the actual tuple is a basis in the prime-local module. -/
theorem mem_intrinsicBasisOpen_iff (y : Fin d → M) (p : PrimeSpectrum R) :
    p ∈ intrinsicBasisOpen y ↔
      ∃ c : Module.Basis (Fin d) (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[R] M),
        ∀ i, c i = (1 : Localization.AtPrime p.asIdeal) ⊗ₜ[R] y i := by
  exact (localized_tuple_basis_iff p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    (TensorProduct.mk R (Localization.AtPrime p.asIdeal) M 1) y).symm

/-- Each point has a principal neighborhood carrying exactly the proposed basis. -/
theorem exists_principal_basis_neighborhood (y : Fin d → M) (p : PrimeSpectrum R)
    (hp : p ∈ intrinsicBasisOpen y) :
    ∃ r : R, r ∉ p.asIdeal ∧
      (∃ c : Module.Basis (Fin d) (Localization.Away r) (Localization.Away r ⊗[R] M),
        ∀ i, c i = (1 : Localization.Away r) ⊗ₜ[R] y i) ∧
      PrimeSpectrum.basicOpen r ≤ intrinsicBasisOpen y := by
  have hp' : Function.Bijective (IsLocalizedModule.map p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (Fin d → R))
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) (tupleLinearMap y)) :=
    (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective _ _).mpr hp
  obtain ⟨r, hr, hb⟩ := Module.FinitePresentation.exists_notMem_bijective (tupleLinearMap y)
    p.asIdeal (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (Fin d → R))
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) hp'
  refine ⟨r, hr, ?_, ?_⟩
  · exact (localized_tuple_basis_iff (.powers r) (Localization.Away r)
      (TensorProduct.mk R (Localization.Away r) M 1) y).mpr hb
  · intro q hq
    change Function.Bijective (LocalizedModule.map q.asIdeal.primeCompl (tupleLinearMap y))
    exact localizedMap_bijective_of_le (.powers r) q.asIdeal.primeCompl
      (Submonoid.powers_le.mpr hq) (tupleLinearMap y) hb

variable {A : Type*} [CommRing A] [Algebra R A] [Module.FinitePresentation R A]

/-- Every global trivialization computes the intrinsic open by its determinant. -/
theorem intrinsicBasisOpen_eq_basisOpen (b : Module.Basis (Fin d) R A) (y : Fin d → A) :
    intrinsicBasisOpen y = basisOpen b y := by
  ext p
  change p ∈ intrinsicBasisOpen y ↔ p ∈ basisOpen b y
  rw [mem_intrinsicBasisOpen_iff, mem_basisOpen_iff]
  rfl

end FLT.Mazur.HilbertChart

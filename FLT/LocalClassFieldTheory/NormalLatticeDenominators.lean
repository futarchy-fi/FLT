/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.IntegralNormalLattice
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.Integer

/-!
# A common denominator for the integral normal lattice

Clearing the finite matrix of coordinates of an integral basis puts one
nonzero base-ring multiple of the entire ring of integers into the
constructed normal lattice.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open scoped nonZeroDivisors

variable (R S K L : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [FiniteDimensional K L] [IsGalois K L]

omit [FaithfulSMul R S] in
/-- Some nonzero base-ring scalar carries all integral elements into the normal lattice. -/
theorem integralNormalLattice_common_denominator :
    ∃ d : R, d ≠ 0 ∧ ∀ x : S, d • algebraMap S L x ∈ integralNormalLattice R K L := by
  classical
  let : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  let : IsIntegralClosure S R L := IsIntegralClosure.of_isIntegrallyClosed S R L
  let : Module.Free R S := IsIntegralClosure.module_free R K L S
  let b := Module.finBasis R S
  let a := integralNormalBasis R K L
  let : Fintype Gal(L/K) := Fintype.ofFinite _
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite R⁰
    (fun p : Fin (Module.finrank R S) × Gal(L/K) => a.repr (algebraMap S L (b p.1)) p.2)
  have hb : ∀ i, (d : R) • algebraMap S L (b i) ∈ integralNormalLattice R K L := by
    intro i
    rw [← a.sum_repr (algebraMap S L (b i)), Finset.smul_sum]
    apply Submodule.sum_mem
    intro g _
    obtain ⟨r, hr⟩ := hd (i, g)
    rw [← smul_assoc, ← hr, IsScalarTower.algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨g, rfl⟩)
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.property, fun x => ?_⟩
  rw [← b.sum_repr x, map_sum, Finset.smul_sum]
  apply Submodule.sum_mem
  intro i _
  change (d : R) • (IsScalarTower.toAlgHom R S L) (b.repr x i • b i) ∈ _
  rw [map_smul, smul_comm]
  exact Submodule.smul_mem _ _ (hb i)

end LocalClassFieldTheory

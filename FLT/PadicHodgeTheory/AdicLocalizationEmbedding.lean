/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AdicLocalizationTopology

/-! # The integral lattice is an open embedded subring of its coefficient localization -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R : Type*} [CommRing R] (r : R) (S : Type*) [CommRing S] [Algebra R S]

/-- Injectivity identifies the pullback of each lattice with the original parameter ideal power. -/
theorem adicLocalizationLattice_preimage (hinj : Function.Injective (algebraMap R S)) (n : ℕ) :
    (algebraMap R S) ⁻¹' (adicLocalizationLattice r S n : Set S) =
      ((Ideal.span {r} ^ n : Ideal R) : Set R) := by
  ext a
  simp only [Set.mem_preimage, mem_adicLocalizationLattice, Ideal.span_singleton_pow,
    SetLike.mem_coe, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, (hinj hb).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, rfl⟩

variable [IsLocalization.Away r S]

/-- The localization induces exactly the original parameter-adic topology. -/
theorem adicLocalization_isInducing [TopologicalSpace R] [IsTopologicalRing R]
    (hR : IsAdic (Ideal.span {r})) (hinj : Function.Injective (algebraMap R S)) :
    let := adicLocalizationTopology r S
    Topology.IsInducing (algebraMap R S) := by
  let := adicLocalizationTopology r S
  let := adicLocalization_isTopologicalRing r S
  apply IsTopologicalAddGroup.isInducing_iff_nhds_zero.mpr
  apply hR.hasBasis_nhds_zero.eq_of_same_basis
  exact ((adicLocalization_hasBasis_nhds_zero r S).comap (algebraMap R S)).congr
    (fun _ ↦ Iff.rfl) (fun n _ ↦ adicLocalizationLattice_preimage r S hinj n)

omit [IsLocalization.Away r S] in
/-- The zeroth integral lattice is precisely the image of R. -/
theorem adicLocalizationLattice_zero :
    (adicLocalizationLattice r S 0 : Set S) = Set.range (algebraMap R S) := by
  ext x
  simp only [SetLike.mem_coe, mem_adicLocalizationLattice, pow_zero, one_mul, Set.mem_range]

/-- The integral image is open in the coefficient topology. -/
theorem adicLocalization_range_isOpen :
    let := adicLocalizationTopology r S
    IsOpen (Set.range (algebraMap R S)) := by
  let := adicLocalizationTopology r S
  rw [← adicLocalizationLattice_zero r S]
  exact ((adicLocalizationBasis r S).openAddSubgroup 0).isOpen'

/-- The integral inclusion is an open embedding, not just a continuous map. -/
theorem adicLocalization_isOpenEmbedding [TopologicalSpace R] [IsTopologicalRing R]
    (hR : IsAdic (Ideal.span {r})) (hinj : Function.Injective (algebraMap R S)) :
    let := adicLocalizationTopology r S
    Topology.IsOpenEmbedding (algebraMap R S) := by
  let := adicLocalizationTopology r S
  exact ⟨⟨adicLocalization_isInducing r S hR hinj, hinj⟩, adicLocalization_range_isOpen r S⟩

end PadicHodgeTheory

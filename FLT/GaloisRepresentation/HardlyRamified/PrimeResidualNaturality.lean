/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.PrimeResidualAlgebra

/-! # Uniqueness and naturality of prime-field reduction -/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

variable (p : ℕ) [Fact p.Prime] (D : Type*)
  [CommRing D] [IsLocalRing D] [Algebra ℤ_[p] D]
  [IsLocalHom (algebraMap ℤ_[p] D)] [IsResidueAlgebra ℤ_[p] D]

/-- The residual prime-field map is unique, without assuming continuity or locality
of the competing map. -/
theorem primeReduction_unique (f : D →+* ZMod p) : f = primeReduction p D := by
  have hfker := IsLocalRing.ker_eq_maximalIdeal f (ZMod.ringHom_surjective f)
  have hfcoeff := primeResidueMap_unique p (f.comp (algebraMap ℤ_[p] D))
  ext x
  obtain ⟨a, ha⟩ := IsResidueAlgebra.exists_sub_mem_maximalIdeal ℤ_[p] x
  have hf : f x = f (algebraMap ℤ_[p] D a) := by
    have hz : x - algebraMap ℤ_[p] D a ∈ RingHom.ker f := hfker.symm ▸ ha
    exact sub_eq_zero.mp (by simpa only [RingHom.mem_ker, map_sub] using hz)
  have hr : primeReduction p D x = primeReduction p D (algebraMap ℤ_[p] D a) := by
    have hz : x - algebraMap ℤ_[p] D a ∈ RingHom.ker (primeReduction p D) :=
      (primeReduction_ker p D).symm ▸ ha
    exact sub_eq_zero.mp (by simpa only [RingHom.mem_ker, map_sub] using hz)
  rw [hf, hr]
  exact (RingHom.congr_fun hfcoeff a).trans
    (RingHom.congr_fun (primeReduction_comp_algebraMap p D) a).symm

/-- Maps between same-residue coefficient algebras commute with prime-field reduction. -/
theorem primeReduction_natural (E : Type*)
    [CommRing E] [IsLocalRing E] [Algebra ℤ_[p] E]
    [IsLocalHom (algebraMap ℤ_[p] E)] [IsResidueAlgebra ℤ_[p] E]
    (f : D →+* E) :
    (primeReduction p E).comp f = primeReduction p D :=
  primeReduction_unique p D _

end GaloisRepresentation.IsHardlyRamified

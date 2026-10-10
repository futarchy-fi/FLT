/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertMonomialFiberBasis
public import FLT.Mazur.HilbertBasisBaseChangeCover

/-!
# Monomial chart neighborhoods for arbitrary finite flat families

Choose monomial images forming a basis at a residue fiber, then use the
intrinsic basis locus to lift those same ambient polynomials to a neighborhood.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

variable (R I : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
variable (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]

/-- Every residue fiber of dimension `d` lies in a chart prescribed by ambient monomials. -/
theorem exists_monomial_basisOpen (p : PrimeSpectrum S) (d : ℕ)
    (hd : Module.finrank p.asIdeal.ResidueField
      (MvPolynomial I p.asIdeal.ResidueField ⧸
        J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d) :
    ∃ m : Fin d → (I →₀ ℕ),
      p ∈ polynomialBasisOpen R I d (fun i ↦ MvPolynomial.monomial (m i) 1) S J := by
  let K := p.asIdeal.ResidueField
  let _ := polynomialQuotient_finitePresentation_baseChange I S J K
  obtain ⟨m, b, hb⟩ := exists_quotient_monomial_basis K I
    (J.map (MvPolynomial.map (algebraMap S K))) d hd
  refine ⟨m, ?_⟩
  apply (mem_intrinsicBasisOpen_iff_residueField _ p).mpr
  apply (polynomialBasisTuple_basis_iff R I d
    (fun i ↦ MvPolynomial.monomial (m i) 1) S K J).mpr
  refine ⟨b, fun i ↦ ?_⟩
  simpa only [polynomialBasisTuple, MvPolynomial.map_monomial, map_one] using (hb i).symm

/-- The selected ambient monomials remain a basis on an actual principal neighborhood. -/
theorem exists_monomial_basisNeighborhood (p : PrimeSpectrum S) (d : ℕ)
    (hd : Module.finrank p.asIdeal.ResidueField
      (MvPolynomial I p.asIdeal.ResidueField ⧸
        J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d) :
    ∃ m : Fin d → (I →₀ ℕ),
      ∃ r : PolynomialBasisNeighborhoods R I d
        (fun i ↦ MvPolynomial.monomial (m i) 1) S J,
        p ∈ PrimeSpectrum.basicOpen r.val := by
  obtain ⟨m, hm⟩ := exists_monomial_basisOpen R I S J p d hd
  obtain ⟨r, hr⟩ := exists_polynomialBasisNeighborhood R I d
    (fun i ↦ MvPolynomial.monomial (m i) 1) S J p hm
  exact ⟨m, r, hr⟩

end FLT.Mazur.HilbertChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertMonomialChartCover

/-!
# Constant residue rank after arbitrary scalar extension

The monomial basis cover pulls back to a cover, so every new residue quotient
has a basis of the same size. Flatness is transported through the actual
polynomial tensor-quotient equivalence.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.HilbertChart

variable (I S : Type*) [CommRing S]
variable (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]
variable (T : Type*) [CommRing T] [Algebra S T]

omit [Module.FinitePresentation S (MvPolynomial I S ⧸ J)] in
/-- The quotient by the actual extended polynomial ideal remains flat. -/
theorem polynomialQuotient_flat_baseChange :
    Module.Flat T (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))) :=
  Module.Flat.of_linearEquiv (polynomialQuotientBaseChangeEquiv I S T J).toLinearEquiv.symm

/-- Constant residue rank is preserved by every scalar extension. -/
theorem polynomialQuotient_residueRank_baseChange (d : ℕ)
    (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
      (MvPolynomial I p.asIdeal.ResidueField ⧸
        J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)
    (q : PrimeSpectrum T) :
    Module.finrank q.asIdeal.ResidueField (MvPolynomial I q.asIdeal.ResidueField ⧸
      (J.map (MvPolynomial.map (algebraMap S T))).map
        (MvPolynomial.map (algebraMap T q.asIdeal.ResidueField))) = d := by
  let _ := polynomialQuotient_finitePresentation_baseChange I S J T
  let _ := polynomialQuotient_flat_baseChange I S J T
  obtain ⟨m, hm⟩ := exists_monomial_basisOpen S I S J
    (PrimeSpectrum.comap (algebraMap S T) q) d (hd _)
  have hq : q ∈ polynomialBasisOpen S I d (fun i ↦ MvPolynomial.monomial (m i) 1)
      T (J.map (MvPolynomial.map (algebraMap S T))) := by
    rw [polynomialBasisOpen_baseChange S I d _ S J T]
    exact hm
  obtain ⟨b, _⟩ := (mem_polynomialBasisOpen_iff_residueField S I d _ T
    (J.map (MvPolynomial.map (algebraMap S T))) q).mp hq
  simpa using Module.finrank_eq_card_basis b

end FLT.Mazur.HilbertChart

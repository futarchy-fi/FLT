/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertMonomialBasisNeighborhood
public import FLT.Mazur.HilbertBasisSchemeCover

/-!
# Covering arbitrary quotient families by monomial Hilbert charts

For a finite flat family of fixed residue rank, the intrinsic monomial basis
opens cover the entire base. This supplies actual classifying neighborhoods
without expressing the family as a sum of sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
variable (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]
variable (d : ℕ)
variable (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
  (MvPolynomial I p.asIdeal.ResidueField ⧸
    J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

include hd in
/-- The monomial basis opens cover every point of a family of the prescribed fiber rank. -/
theorem monomialBasisOpen_iSup_eq_top :
    (⨆ m : Fin d → (I →₀ ℕ), polynomialBasisOpen R I d
      (fun i ↦ MvPolynomial.monomial (m i) 1) S J) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨m, hm⟩ := exists_monomial_basisOpen R I S J p d (hd p)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨m, hm⟩

/-- An actual scheme open cover of the base by all intrinsic monomial basis loci. -/
def monomialBasisSchemeCover : (Spec (.of S)).OpenCover where
  I₀ := Fin d → (I →₀ ℕ)
  X m := polynomialBasisScheme R I d (fun i ↦ MvPolynomial.monomial (m i) 1) S J
  f m := Scheme.Opens.ι (X := Spec (.of S))
    (polynomialBasisOpen R I d (fun i ↦ MvPolynomial.monomial (m i) 1) S J)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun p ↦ ?_, ?_⟩
    · obtain ⟨m, hm⟩ := exists_monomial_basisOpen R I S J p d (hd p)
      exact ⟨m, ⟨p, hm⟩, rfl⟩
    · intro m
      change IsOpenImmersion (Scheme.Opens.ι (X := Spec (.of S))
        (polynomialBasisOpen R I d (fun i ↦ MvPolynomial.monomial (m i) 1) S J))
      infer_instance

/-- Actual principal neighborhoods with monomial chart parameters cover the whole base. -/
def monomialPrincipalSchemeCover : (Spec (.of S)).OpenCover :=
  (monomialBasisSchemeCover R I S J d hd).bind fun m ↦
    polynomialBasisSchemeCover R I d (fun i ↦ MvPolynomial.monomial (m i) 1) S J

end FLT.Mazur.HilbertChart

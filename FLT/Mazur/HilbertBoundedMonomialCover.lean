/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundedMonomialBasis
public import FLT.Mazur.HilbertMonomialChartCover

/-!
# Uniform bounded monomial charts on actual quotient families

The rank bound gives a finite set of candidate basis tuples whenever the
ambient variable set is finite. Their intrinsic basis opens cover any finite
flat family of rank `d`, over an arbitrary coefficient algebra. The cover
retains the actual quotient ideals and does not choose one basis for all fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false

universe u
variable (R I S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (J : Ideal (MvPolynomial I S)) [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
  [Module.Flat S (MvPolynomial I S ⧸ J)]

/-- A basis at any residue fiber can be chosen with the uniform ambient degree bound. -/
theorem exists_boundedMonomial_basisOpen (p : PrimeSpectrum S) (d : ℕ)
    (hd : Module.finrank p.asIdeal.ResidueField
      (MvPolynomial I p.asIdeal.ResidueField ⧸
        J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d) :
    ∃ m : Fin d → BoundedHilbertMonomials I d,
      p ∈ polynomialBasisOpen R I d (fun i ↦ MvPolynomial.monomial (m i).val 1) S J := by
  let K := p.asIdeal.ResidueField
  let _ := polynomialQuotient_finitePresentation_baseChange I S J K
  obtain ⟨m, b, hb⟩ := exists_quotient_boundedMonomial_basis K I
    (J.map (MvPolynomial.map (algebraMap S K))) d hd
  refine ⟨m, ?_⟩
  apply (mem_intrinsicBasisOpen_iff_residueField _ p).mpr
  apply (polynomialBasisTuple_basis_iff R I d
    (fun i ↦ MvPolynomial.monomial (m i).val 1) S K J).mpr
  refine ⟨b, fun i ↦ ?_⟩
  simpa only [polynomialBasisTuple, MvPolynomial.map_monomial, map_one] using (hb i).symm

variable (d : ℕ)
  (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
    (MvPolynomial I p.asIdeal.ResidueField ⧸
      J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

include hd in
/-- Uniformly bounded monomial basis opens cover the full test base. -/
theorem boundedMonomialBasisOpen_iSup_eq_top :
    (⨆ m : Fin d → BoundedHilbertMonomials I d, polynomialBasisOpen R I d
      (fun i ↦ MvPolynomial.monomial (m i).val 1) S J) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨m, hm⟩ := exists_boundedMonomial_basisOpen R I S J p d (hd p)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨m, hm⟩

/-- The actual scheme cover uses only bounded ambient monomial tuples. -/
def boundedMonomialBasisSchemeCover : (Spec (.of S)).OpenCover where
  I₀ := Fin d → BoundedHilbertMonomials I d
  X m := polynomialBasisScheme R I d (fun i ↦ MvPolynomial.monomial (m i).val 1) S J
  f m := Scheme.Opens.ι (X := Spec (.of S))
    (polynomialBasisOpen R I d (fun i ↦ MvPolynomial.monomial (m i).val 1) S J)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun p ↦ ?_, fun m ↦ inferInstance⟩
    obtain ⟨m, hm⟩ := exists_boundedMonomial_basisOpen R I S J p d (hd p)
    exact ⟨m, ⟨p, hm⟩, rfl⟩

instance [Finite I] : Finite (boundedMonomialBasisSchemeCover R I S J d hd).I₀ :=
  inferInstanceAs (Finite (Fin d → BoundedHilbertMonomials I d))

end FLT.Mazur.HilbertChart

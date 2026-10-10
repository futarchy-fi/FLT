/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialBasisOpen
public import FLT.Mazur.HilbertIntrinsicBasisBaseChange
public import FLT.Mazur.HilbertIntrinsicBasisEquiv

/-!
# Naturality of the actual polynomial basis locus

Residue-field detection and arbitrary base change apply to the extended
ambient ideal itself, via the tensor-quotient equivalence.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

variable (R : Type*) [CommRing R] (I : Type*) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type*) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]

/-- The prescribed polynomial basis is detected in the actual residue-field quotient. -/
theorem mem_polynomialBasisOpen_iff_residueField (p : PrimeSpectrum S) :
    p ∈ polynomialBasisOpen R I d w S J ↔
      ∃ b : Module.Basis (Fin d) p.asIdeal.ResidueField
        (MvPolynomial I p.asIdeal.ResidueField ⧸
          J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))),
        ∀ i, polynomialBasisTuple R I d w p.asIdeal.ResidueField
          (J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) i = b i := by
  rw [polynomialBasisOpen, mem_intrinsicBasisOpen_iff_residueField]
  exact polynomialBasisTuple_basis_iff R I d w S p.asIdeal.ResidueField J

variable (T : Type*) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

omit [Module.Flat S (MvPolynomial I S ⧸ J)] in
/-- Finite presentation holds for the actual quotient by the extended ideal. -/
theorem polynomialQuotient_finitePresentation_baseChange :
    Module.FinitePresentation T
      (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))) :=
  Module.FinitePresentation.of_equiv (polynomialQuotientBaseChangeEquiv I S T J).toLinearEquiv

/-- Extending the ambient ideal pulls back exactly the intrinsic polynomial basis open. -/
theorem polynomialBasisOpen_baseChange :
    let _ := polynomialQuotient_finitePresentation_baseChange I S J T
    polynomialBasisOpen R I d w T (J.map (MvPolynomial.map (algebraMap S T))) =
      TopologicalSpace.Opens.comap
        ⟨PrimeSpectrum.comap (algebraMap S T), PrimeSpectrum.continuous_comap _⟩
        (polynomialBasisOpen R I d w S J) := by
  let _ := polynomialQuotient_finitePresentation_baseChange I S J T
  dsimp only
  let e := (polynomialQuotientBaseChangeEquiv I S T J).toLinearEquiv
  have he : polynomialBasisTuple R I d w T (J.map (MvPolynomial.map (algebraMap S T))) =
      e ∘ (fun i ↦ (1 : T) ⊗ₜ[S] polynomialBasisTuple R I d w S J i) := by
    funext i
    exact (polynomialBasisTuple_baseChange R I d w S T J i).symm
  unfold polynomialBasisOpen
  rw [he, intrinsicBasisOpen_equiv, intrinsicBasisOpen_baseChange]

end FLT.Mazur.HilbertChart

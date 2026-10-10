/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertIntrinsicBasisOpen
public import FLT.Mazur.HilbertPolynomialQuotientBaseChange

/-!
# The intrinsic open for actual ambient polynomial evaluations

The tuple is evaluated in an arbitrary polynomial quotient. After base change,
its basis condition is exactly the prescribed-basis condition for the extended
ideal, using the actual tensor-quotient isomorphism.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

variable (R : Type*) [CommRing R] (I : Type*) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type*) [CommRing S] [Algebra R S]

/-- The prescribed ambient polynomials evaluated in the actual quotient family. -/
def polynomialBasisTuple (J : Ideal (MvPolynomial I S)) (i : Fin d) :
    MvPolynomial I S ⧸ J :=
  Ideal.Quotient.mk J (MvPolynomial.map (algebraMap R S) (w i))

variable (T : Type*) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- The tensor-quotient comparison preserves each of the prescribed polynomial images. -/
theorem polynomialBasisTuple_baseChange (J : Ideal (MvPolynomial I S)) (i : Fin d) :
    polynomialQuotientBaseChangeEquiv I S T J
      ((1 : T) ⊗ₜ[S] polynomialBasisTuple R I d w S J i) =
      polynomialBasisTuple R I d w T (J.map (MvPolynomial.map (algebraMap S T))) i := by
  rw [polynomialBasisTuple, polynomialQuotientBaseChangeEquiv_tmul,
    one_smul, MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq R S T]
  rfl

/-- The basis condition is for the actual extended ambient ideal. -/
theorem polynomialBasisTuple_basis_iff (J : Ideal (MvPolynomial I S)) :
    (∃ b : Module.Basis (Fin d) T (T ⊗[S] (MvPolynomial I S ⧸ J)),
      ∀ i, b i = (1 : T) ⊗ₜ[S] polynomialBasisTuple R I d w S J i) ↔
    ∃ b : Module.Basis (Fin d) T
      (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))),
      ∀ i, polynomialBasisTuple R I d w T
        (J.map (MvPolynomial.map (algebraMap S T))) i = b i := by
  let e := polynomialQuotientBaseChangeEquiv I S T J
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b.map e.toLinearEquiv, fun i ↦ ?_⟩
    rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, hb]
    exact (polynomialBasisTuple_baseChange R I d w S T J i).symm
  · rintro ⟨b, hb⟩
    refine ⟨b.map e.symm.toLinearEquiv, fun i ↦ ?_⟩
    rw [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, ← hb]
    apply e.injective
    rw [AlgEquiv.apply_symm_apply]
    exact (polynomialBasisTuple_baseChange R I d w S T J i).symm

variable (J : Ideal (MvPolynomial I S)) [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]

/-- The actual basis open of an arbitrary finitely presented quotient family. -/
def polynomialBasisOpen : TopologicalSpace.Opens (PrimeSpectrum S) :=
  intrinsicBasisOpen (polynomialBasisTuple R I d w S J)

/-- At a prime, membership means the extended ideal lies in the prescribed-basis chart. -/
theorem mem_polynomialBasisOpen_iff (p : PrimeSpectrum S) :
    p ∈ polynomialBasisOpen R I d w S J ↔
      ∃ b : Module.Basis (Fin d) (Localization.AtPrime p.asIdeal)
        (MvPolynomial I (Localization.AtPrime p.asIdeal) ⧸
          J.map (MvPolynomial.map (algebraMap S (Localization.AtPrime p.asIdeal)))),
        ∀ i, polynomialBasisTuple R I d w (Localization.AtPrime p.asIdeal)
          (J.map (MvPolynomial.map (algebraMap S (Localization.AtPrime p.asIdeal)))) i = b i := by
  rw [polynomialBasisOpen, mem_intrinsicBasisOpen_iff]
  exact polynomialBasisTuple_basis_iff R I d w S (Localization.AtPrime p.asIdeal) J

end FLT.Mazur.HilbertChart

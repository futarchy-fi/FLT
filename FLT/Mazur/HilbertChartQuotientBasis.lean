/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartClassifyingMap

/-!
# Arbitrary ideals in a prescribed-basis Hilbert chart

The input is an actual ideal in the ambient polynomial ring whose quotient has
the specified polynomial basis. There is no assumption of a classifying map.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type*) [CommRing S] [Algebra R S]

/-- The ambient generators in an actual polynomial quotient. -/
def quotientGenerator (J : Ideal (MvPolynomial I S)) (i : I) : MvPolynomial I S ⧸ J :=
  Ideal.Quotient.mk J (MvPolynomial.X i)

/-- Original polynomial evaluation is the actual quotient of coefficient extension. -/
theorem quotientGenerator_evaluation (J : Ideal (MvPolynomial I S)) (p : MvPolynomial I R) :
    MvPolynomial.aeval (quotientGenerator I S J) p =
      Ideal.Quotient.mk J (MvPolynomial.map (algebraMap R S) p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.aeval_C, MvPolynomial.map_C]
    rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.map_X, hp, quotientGenerator]

/-- The actual ideals whose specified ambient polynomials form a quotient basis. -/
def PrescribedBasisIdeals := {J : Ideal (MvPolynomial I S) //
  ∃ b : Module.Basis (Fin d) S (MvPolynomial I S ⧸ J),
    ∀ i, Ideal.Quotient.mk J (MvPolynomial.map (algebraMap R S) (w i)) = b i}

/-- Choose the actual basis witnessed by membership in the prescribed-basis chart. -/
def quotientBasis (J : PrescribedBasisIdeals R I d w S) :
    Module.Basis (Fin d) S (MvPolynomial I S ⧸ J.val) := Classical.choose J.property

/-- The chosen quotient basis has the required original polynomial evaluations. -/
theorem quotientBasis_spec (J : PrescribedBasisIdeals R I d w S) (i : Fin d) :
    MvPolynomial.aeval (quotientGenerator I S J.val) (w i) = quotientBasis R I d w S J i := by
  rw [quotientGenerator_evaluation]
  exact Classical.choose_spec J.property i

/-- The classifying point of an arbitrary actual prescribed-basis quotient ideal. -/
def idealClassifyingMap (J : PrescribedBasisIdeals R I d w S) : ChartRing R I d w →ₐ[R] S :=
  classifyingMap R I d (quotientBasis R I d w S J) (quotientGenerator I S J.val) w
    (quotientBasis_spec R I d w S J)

/-- Evaluation over the test ring is exactly the canonical quotient homomorphism. -/
theorem quotientGenerator_aeval (J : Ideal (MvPolynomial I S)) :
    MvPolynomial.aeval (quotientGenerator I S J) = Ideal.Quotient.mkₐ S J := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [MvPolynomial.aeval_X]
  rfl

end FLT.Mazur.HilbertChart

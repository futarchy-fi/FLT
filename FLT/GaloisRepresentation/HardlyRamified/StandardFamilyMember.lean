/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.RankTwoFraming
public import FLT.GaloisRepresentation.HardlyRamified.PadicClosureScalars
public import FLT.GaloisRepresentation.HardlyRamified.CyclotomicTrivialBaseChange
public import FLT.GaloisRepresentation.HardlyRamified.CyclotomicTrivialHardlyRamified
public import FLT.Deformations.RepresentationTheory.GaloisRepFamily

/-! # Framed standard members of the compatible family -/

@[expose] public noncomputable section
namespace GaloisRepresentation
variable (p : ℕ) [Fact p.Prime]

/-- The actual scalar extension and framing of the standard integral member. -/
def standardFamilyMember :
    GaloisRep ℚ (AlgebraicClosure ℚ_[p]) (Fin 2 → AlgebraicClosure ℚ_[p]) :=
  ((cyclotomicTrivial p).baseChange (AlgebraicClosure ℚ_[p])).conj
    (rankTwoFrame (AlgebraicClosure ℚ_[p]) (cyclotomicTrivial_rank p))

/-- The framed standard member is unramified away from its coefficient prime. -/
theorem standardFamilyMember_unramified (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    (standardFamilyMember p).IsUnramifiedAt hq.toHeightOneSpectrumRingOfIntegersRat := by
  let := cyclotomicTrivial_unramified p q hq hqp
  unfold standardFamilyMember
  infer_instance

/-- Its good Frobenius polynomial is defined over the rational numbers. -/
theorem standardFamilyMember_frobenius (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) :
    ((standardFamilyMember p).toLocal hq.toHeightOneSpectrumRingOfIntegersRat
      (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).charpoly =
      (Polynomial.X - 1) * (Polynomial.X - Polynomial.C (q : AlgebraicClosure ℚ_[p])) := by
  rw [standardFamilyMember, cyclotomicTrivial_framed_frobenius p _ (algebraMap ℚ _)
    _ q hq hqp]
  simp [cyclotomicTrivialPolynomial]

end GaloisRepresentation

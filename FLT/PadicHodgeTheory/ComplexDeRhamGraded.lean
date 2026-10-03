/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicLogOrder
public import FLT.PadicHodgeTheory.PrincipalGradedPiece

/-! # Nonnegative de Rham graded pieces have actual C_p coordinates -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The actual nonnegative graded quotient (t^n)/(t^(n+1)). -/
abbrev ComplexDeRhamGradedPiece (n : ℕ) := PrincipalGradedPiece (complexCyclotomicLog p) n

/-- The residue identification uses the original completed theta map. -/
def complexDeRhamLogResidueEquiv :
    (ComplexBDeRhamPlus p ⧸ Ideal.span {complexCyclotomicLog p}) ≃+* ℂ_[p] :=
  (Ideal.quotEquivOfEq (show Ideal.span {complexCyclotomicLog p} =
      RingHom.ker (complexDeRhamTheta p) by
        rw [complexDeRhamTheta_ker, complexCyclotomicLog_span, complexDeRham_maximalIdeal])).trans
    (RingHom.quotientKerEquivOfSurjective (complexDeRhamTheta_surjective p))

/-- Dividing by t^n and applying theta identifies the actual graded quotient with C_p. -/
def complexDeRhamGradedCoordinate (n : ℕ) : ComplexDeRhamGradedPiece p n ≃+ ℂ_[p] :=
  (principalGradedEquiv (complexCyclotomicLog_ne_zero p) n).symm.toAddEquiv.trans
    (complexDeRhamLogResidueEquiv p).toAddEquiv

/-- A coefficient a represents the class of a*t^n. -/
def complexDeRhamGradedRepresentative (n : ℕ) (a : ComplexBDeRhamPlus p) :
    ComplexDeRhamGradedPiece p n :=
  (principalGradedSubmodule (complexCyclotomicLog p) n).mkQ
    (principalPowerEquiv (complexCyclotomicLog_ne_zero p) n a)

/-- The graded coordinate of a*t^n is exactly theta(a). -/
theorem complexDeRhamGradedCoordinate_representative (n : ℕ) (a : ComplexBDeRhamPlus p) :
    complexDeRhamGradedCoordinate p n (complexDeRhamGradedRepresentative p n a) =
      complexDeRhamTheta p a := by
  unfold complexDeRhamGradedRepresentative complexDeRhamGradedCoordinate
  rw [← principalGradedEquiv_mk]
  change complexDeRhamLogResidueEquiv p
    ((principalGradedEquiv (complexCyclotomicLog_ne_zero p) n).symm
      (principalGradedEquiv (complexCyclotomicLog_ne_zero p) n (Submodule.Quotient.mk a))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- Every actual graded class has a coefficient representative. -/
theorem complexDeRhamGradedRepresentative_surjective (n : ℕ) :
    Function.Surjective (complexDeRhamGradedRepresentative p n) := by
  intro x
  obtain ⟨a, ha⟩ := complexDeRhamTheta_surjective p (complexDeRhamGradedCoordinate p n x)
  refine ⟨a, (complexDeRhamGradedCoordinate p n).injective ?_⟩
  rw [complexDeRhamGradedCoordinate_representative, ha]

end PadicHodgeTheory

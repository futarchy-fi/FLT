/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexDeRhamFractionField
public import FLT.PadicHodgeTheory.ComplexDeRhamGraded
public import FLT.PadicHodgeTheory.FractionalPrincipalGraded
public import FLT.PadicHodgeTheory.ComplexPadicScalarResidue

/-! # C_p coordinates for every integer graded piece of the actual de Rham field -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The integer filtration is formed inside the existing B_dR. -/
abbrev ComplexDeRhamIntegerFiltration (n : ℤ) :=
  fractionalPrincipalFiltration (K := ComplexBDeRham p) (complexCyclotomicLog p) n

/-- The actual quotient of integer levels n and n+1. -/
abbrev ComplexDeRhamIntegerGradedPiece (n : ℤ) :=
  FractionalPrincipalGradedPiece (K := ComplexBDeRham p) (complexCyclotomicLog p) n

/-- Dividing by the original t^n and applying original theta gives C_p coordinates. -/
def complexDeRhamIntegerGradedCoordinate (n : ℤ) :
    ComplexDeRhamIntegerGradedPiece p n ≃+ ℂ_[p] :=
  (fractionalPrincipalGradedEquiv (K := ComplexBDeRham p)
      (complexCyclotomicLog_ne_zero p) n).symm.toAddEquiv.trans
    (complexDeRhamLogResidueEquiv p).toAddEquiv

/-- A coefficient represents its actual multiple of t^n, even at negative n. -/
def complexDeRhamIntegerGradedRepresentative (n : ℤ) (a : ComplexBDeRhamPlus p) :
    ComplexDeRhamIntegerGradedPiece p n :=
  (fractionalPrincipalNext (K := ComplexBDeRham p) (complexCyclotomicLog p) n).mkQ
    (fractionalPrincipalEquiv (K := ComplexBDeRham p) (complexCyclotomicLog_ne_zero p) n a)

/-- The coordinate of the original field representative a*t^n is theta(a). -/
theorem complexDeRhamIntegerGradedCoordinate_representative (n : ℤ) (a : ComplexBDeRhamPlus p) :
    complexDeRhamIntegerGradedCoordinate p n (complexDeRhamIntegerGradedRepresentative p n a) =
      complexDeRhamTheta p a := by
  unfold complexDeRhamIntegerGradedRepresentative complexDeRhamIntegerGradedCoordinate
  rw [← fractionalPrincipalGradedEquiv_mk]
  change complexDeRhamLogResidueEquiv p
    ((fractionalPrincipalGradedEquiv (K := ComplexBDeRham p)
      (complexCyclotomicLog_ne_zero p) n).symm
      (fractionalPrincipalGradedEquiv (K := ComplexBDeRham p) (complexCyclotomicLog_ne_zero p) n
        (Submodule.Quotient.mk a))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- Every integer graded class has a coefficient in the original B_dR+. -/
theorem complexDeRhamIntegerGradedRepresentative_surjective (n : ℤ) :
    Function.Surjective (complexDeRhamIntegerGradedRepresentative p n) := by
  intro x
  obtain ⟨a, ha⟩ := complexDeRhamTheta_surjective p (complexDeRhamIntegerGradedCoordinate p n x)
  refine ⟨a, (complexDeRhamIntegerGradedCoordinate p n).injective ?_⟩
  rw [complexDeRhamIntegerGradedCoordinate_representative, ha]

/-- Original B_dR+ scalars act through theta on every integer graded piece. -/
theorem complexDeRhamIntegerGradedCoordinate_smul (n : ℤ) (a : ComplexBDeRhamPlus p)
    (x : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedCoordinate p n (a • x) =
      complexDeRhamTheta p a * complexDeRhamIntegerGradedCoordinate p n x := by
  obtain ⟨b, rfl⟩ := complexDeRhamIntegerGradedRepresentative_surjective p n x
  have he : a • complexDeRhamIntegerGradedRepresentative p n b =
      complexDeRhamIntegerGradedRepresentative p n (a * b) := by
    unfold complexDeRhamIntegerGradedRepresentative
    rw [← map_smul, ← map_smul, smul_eq_mul]
  rw [he, complexDeRhamIntegerGradedCoordinate_representative,
    complexDeRhamIntegerGradedCoordinate_representative, map_mul]

/-- The Q_p scalar formula uses its existing period embedding. -/
theorem complexDeRhamIntegerGradedCoordinate_padic_smul (n : ℤ) (a : ℚ_[p])
    (x : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedCoordinate p n (complexPadicToDeRham p a • x) =
      algebraMap ℚ_[p] ℂ_[p] a * complexDeRhamIntegerGradedCoordinate p n x := by
  rw [complexDeRhamIntegerGradedCoordinate_smul, complexPadicToDeRham_theta]

end PadicHodgeTheory

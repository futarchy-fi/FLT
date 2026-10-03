/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexIntegerGraded
public import FLT.PadicHodgeTheory.FractionalPrincipalGradedProduct

/-! # Multiplication and scalar compatibility for all integer de Rham graded pieces -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The product induced by the actual multiplication of field representatives. -/
def complexDeRhamIntegerGradedMul (m n : ℤ)
    (x : ComplexDeRhamIntegerGradedPiece p m) (y : ComplexDeRhamIntegerGradedPiece p n) :
    ComplexDeRhamIntegerGradedPiece p (m + n) :=
  fractionalPrincipalGradedMul (complexCyclotomicLog_ne_zero p) m n x y

/-- Coefficients multiply using the original completed-ring multiplication. -/
theorem complexDeRhamIntegerGradedMul_representative (m n : ℤ) (a b : ComplexBDeRhamPlus p) :
    complexDeRhamIntegerGradedMul p m n
      (complexDeRhamIntegerGradedRepresentative p m a)
      (complexDeRhamIntegerGradedRepresentative p n b) =
      complexDeRhamIntegerGradedRepresentative p (m + n) (a * b) :=
  fractionalPrincipalGradedMul_representative (complexCyclotomicLog_ne_zero p) m n a b

/-- The integer graded product comes from actual B_dR multiplication before quotienting. -/
theorem complexDeRhamIntegerGradedMul_mk (m n : ℤ)
    (x : ComplexDeRhamIntegerFiltration p m) (y : ComplexDeRhamIntegerFiltration p n) :
    complexDeRhamIntegerGradedMul p m n
      ((fractionalPrincipalNext (K := ComplexBDeRham p) (complexCyclotomicLog p) m).mkQ x)
      ((fractionalPrincipalNext (K := ComplexBDeRham p) (complexCyclotomicLog p) n).mkQ y) =
      (fractionalPrincipalNext (K := ComplexBDeRham p) (complexCyclotomicLog p) (m + n)).mkQ
        ⟨(x : ComplexBDeRham p) * y, fractionalPrincipalFiltration_mul_mem
          (complexCyclotomicLog p) (complexCyclotomicLog_ne_zero p) m n x.property y.property⟩ :=
  fractionalPrincipalGradedMul_mk (complexCyclotomicLog_ne_zero p) m n x y

/-- Original theta turns multiplication at arbitrary integer degrees into C_p multiplication. -/
theorem complexDeRhamIntegerGradedCoordinate_mul (m n : ℤ)
    (x : ComplexDeRhamIntegerGradedPiece p m) (y : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedCoordinate p (m + n) (complexDeRhamIntegerGradedMul p m n x y) =
      complexDeRhamIntegerGradedCoordinate p m x * complexDeRhamIntegerGradedCoordinate p n y := by
  obtain ⟨a, rfl⟩ := complexDeRhamIntegerGradedRepresentative_surjective p m x
  obtain ⟨b, rfl⟩ := complexDeRhamIntegerGradedRepresentative_surjective p n y
  rw [complexDeRhamIntegerGradedMul_representative,
    complexDeRhamIntegerGradedCoordinate_representative,
    complexDeRhamIntegerGradedCoordinate_representative,
    complexDeRhamIntegerGradedCoordinate_representative, map_mul]

/-- The degree-adding product is additive in the first variable. -/
theorem complexDeRhamIntegerGradedMul_add_left (m n : ℤ)
    (x x' : ComplexDeRhamIntegerGradedPiece p m) (y : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedMul p m n (x + x') y =
      complexDeRhamIntegerGradedMul p m n x y + complexDeRhamIntegerGradedMul p m n x' y := by
  apply (complexDeRhamIntegerGradedCoordinate p (m + n)).injective
  simp only [complexDeRhamIntegerGradedCoordinate_mul, map_add, add_mul]

/-- The degree-adding product is additive in the second variable. -/
theorem complexDeRhamIntegerGradedMul_add_right (m n : ℤ)
    (x : ComplexDeRhamIntegerGradedPiece p m) (y y' : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedMul p m n x (y + y') =
      complexDeRhamIntegerGradedMul p m n x y + complexDeRhamIntegerGradedMul p m n x y' := by
  apply (complexDeRhamIntegerGradedCoordinate p (m + n)).injective
  simp only [complexDeRhamIntegerGradedCoordinate_mul, map_add, mul_add]

/-- The product respects the original B_dR+ scalar action. -/
theorem complexDeRhamIntegerGradedMul_smul_left (m n : ℤ) (a : ComplexBDeRhamPlus p)
    (x : ComplexDeRhamIntegerGradedPiece p m) (y : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedMul p m n (a • x) y =
      a • complexDeRhamIntegerGradedMul p m n x y := by
  apply (complexDeRhamIntegerGradedCoordinate p (m + n)).injective
  simp only [complexDeRhamIntegerGradedCoordinate_mul,
    complexDeRhamIntegerGradedCoordinate_smul, mul_assoc]

end PadicHodgeTheory

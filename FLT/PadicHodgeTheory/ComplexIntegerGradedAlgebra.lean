/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexIntegerGradedScalars

/-! # Algebra laws for the actual integer de Rham graded quotients -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Reindexing a graded piece along equality leaves its underlying quotient unchanged. -/
def complexDeRhamIntegerGradedCast {m n : ℤ} (h : m = n) :
    ComplexDeRhamIntegerGradedPiece p m ≃ₗ[ℂ_[p]] ComplexDeRhamIntegerGradedPiece p n := by
  subst n
  exact LinearEquiv.refl _ _

/-- Reindexing preserves the canonical coordinate. -/
theorem complexDeRhamIntegerGradedCoordinate_cast {m n : ℤ} (h : m = n)
    (x : ComplexDeRhamIntegerGradedPiece p m) :
    complexDeRhamIntegerGradedCoordinate p n (complexDeRhamIntegerGradedCast p h x) =
      complexDeRhamIntegerGradedCoordinate p m x := by
  subst n
  rfl

/-- The actual degree-adding product is associative, with the necessary degree reindexing. -/
theorem complexDeRhamIntegerGradedMul_assoc (l m n : ℤ)
    (x : ComplexDeRhamIntegerGradedPiece p l) (y : ComplexDeRhamIntegerGradedPiece p m)
    (z : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedCast p (add_assoc l m n)
      (complexDeRhamIntegerGradedMul p (l + m) n (complexDeRhamIntegerGradedMul p l m x y) z) =
      complexDeRhamIntegerGradedMul p l (m + n) x (complexDeRhamIntegerGradedMul p m n y z) := by
  apply (complexDeRhamIntegerGradedCoordinate p (l + (m + n))).injective
  simp only [complexDeRhamIntegerGradedCoordinate_cast,
    complexDeRhamIntegerGradedCoordinate_mul, mul_assoc]

/-- The actual degree-adding product is commutative after swapping its degree labels. -/
theorem complexDeRhamIntegerGradedMul_comm (m n : ℤ)
    (x : ComplexDeRhamIntegerGradedPiece p m) (y : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedCast p (add_comm m n) (complexDeRhamIntegerGradedMul p m n x y) =
      complexDeRhamIntegerGradedMul p n m y x := by
  apply (complexDeRhamIntegerGradedCoordinate p (n + m)).injective
  simp only [complexDeRhamIntegerGradedCoordinate_cast,
    complexDeRhamIntegerGradedCoordinate_mul]
  exact mul_comm _ _

/-- The original unit in the degree-zero quotient is a left identity. -/
theorem complexDeRhamIntegerGradedMul_one_left (n : ℤ)
    (x : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedCast p (zero_add n)
      (complexDeRhamIntegerGradedMul p 0 n (complexDeRhamIntegerGradedRepresentative p 0 1) x) =
      x := by
  apply (complexDeRhamIntegerGradedCoordinate p n).injective
  simp only [complexDeRhamIntegerGradedCoordinate_cast,
    complexDeRhamIntegerGradedCoordinate_mul,
    complexDeRhamIntegerGradedCoordinate_representative, map_one, one_mul]

/-- The original unit in the degree-zero quotient is a right identity. -/
theorem complexDeRhamIntegerGradedMul_one_right (n : ℤ)
    (x : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedCast p (add_zero n)
      (complexDeRhamIntegerGradedMul p n 0 x (complexDeRhamIntegerGradedRepresentative p 0 1)) =
      x := by
  apply (complexDeRhamIntegerGradedCoordinate p n).injective
  simp only [complexDeRhamIntegerGradedCoordinate_cast,
    complexDeRhamIntegerGradedCoordinate_mul,
    complexDeRhamIntegerGradedCoordinate_representative, map_one, mul_one]

/-- The original field action preserves the multiplication of graded classes. -/
theorem complexDeRhamIntegerGradedMul_galois (σ : PadicGalois p) (m n : ℤ)
    (x : ComplexDeRhamIntegerGradedPiece p m) (y : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedGalois p σ (m + n) (complexDeRhamIntegerGradedMul p m n x y) =
      complexDeRhamIntegerGradedMul p m n
        (complexDeRhamIntegerGradedGalois p σ m x) (complexDeRhamIntegerGradedGalois p σ n y) := by
  have hc : algebraMap ℚ_[p] ℂ_[p]
      ((cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).val : ℚ_[p]) ≠ 0 := by
    apply (map_ne_zero_iff _ (algebraMap ℚ_[p] ℂ_[p]).injective).mpr
    exact PadicInt.coe_ne_zero.mpr (cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv).ne_zero
  apply (complexDeRhamIntegerGradedCoordinate p (m + n)).injective
  simp only [complexDeRhamIntegerGradedCoordinate_mul,
    complexDeRhamIntegerGradedCoordinate_galois, map_mul, zpow_add₀ hc]
  ring

end PadicHodgeTheory

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexIntegerGradedGalois
public import FLT.PadicHodgeTheory.ComplexIntegerGradedProduct
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # The residue-field module structure on actual integer de Rham graded pieces -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Transport residue scalars along the proved coordinate equivalence. -/
instance instModuleComplexDeRhamIntegerGraded (n : ℤ) :
    Module ℂ_[p] (ComplexDeRhamIntegerGradedPiece p n) :=
  (complexDeRhamIntegerGradedCoordinate p n).module ℂ_[p]

/-- The actual integer graded quotient is a one-dimensional C_p module. -/
def complexDeRhamIntegerGradedLinearEquiv (n : ℤ) :
    ComplexDeRhamIntegerGradedPiece p n ≃ₗ[ℂ_[p]] ℂ_[p] :=
  (complexDeRhamIntegerGradedCoordinate p n).linearEquiv ℂ_[p]

/-- C_p scalars multiply the canonical coordinates. -/
theorem complexDeRhamIntegerGradedCoordinate_complex_smul (n : ℤ) (c : ℂ_[p])
    (x : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedCoordinate p n (c • x) =
      c * complexDeRhamIntegerGradedCoordinate p n x :=
  (complexDeRhamIntegerGradedLinearEquiv p n).map_smul c x

/-- The residue-field action agrees with the pre-existing completed-ring scalar action. -/
theorem complexDeRhamIntegerGraded_theta_smul (n : ℤ) (a : ComplexBDeRhamPlus p)
    (x : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamTheta p a • x = a • x := by
  apply (complexDeRhamIntegerGradedCoordinate p n).injective
  rw [complexDeRhamIntegerGradedCoordinate_complex_smul,
    complexDeRhamIntegerGradedCoordinate_smul]

/-- The dimension over the actual residue field is one at every integer level. -/
theorem complexDeRhamIntegerGraded_finrank (n : ℤ) :
    Module.finrank ℂ_[p] (ComplexDeRhamIntegerGradedPiece p n) = 1 := by
  rw [(complexDeRhamIntegerGradedLinearEquiv p n).finrank_eq, Module.finrank_self]

/-- Graded multiplication is C_p-linear in the first variable. -/
theorem complexDeRhamIntegerGradedMul_complex_smul_left (m n : ℤ) (c : ℂ_[p])
    (x : ComplexDeRhamIntegerGradedPiece p m) (y : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedMul p m n (c • x) y =
      c • complexDeRhamIntegerGradedMul p m n x y := by
  apply (complexDeRhamIntegerGradedCoordinate p (m + n)).injective
  simp only [complexDeRhamIntegerGradedCoordinate_mul,
    complexDeRhamIntegerGradedCoordinate_complex_smul, mul_assoc]

/-- Graded multiplication is C_p-linear in the second variable. -/
theorem complexDeRhamIntegerGradedMul_complex_smul_right (m n : ℤ) (c : ℂ_[p])
    (x : ComplexDeRhamIntegerGradedPiece p m) (y : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedMul p m n x (c • y) =
      c • complexDeRhamIntegerGradedMul p m n x y := by
  apply (complexDeRhamIntegerGradedCoordinate p (m + n)).injective
  simp only [complexDeRhamIntegerGradedCoordinate_mul,
    complexDeRhamIntegerGradedCoordinate_complex_smul]
  ring

/-- The original descended Galois action is semilinear for the actual C_p action. -/
theorem complexDeRhamIntegerGradedGalois_complex_smul (σ : PadicGalois p) (n : ℤ) (c : ℂ_[p])
    (x : ComplexDeRhamIntegerGradedPiece p n) :
    complexDeRhamIntegerGradedGalois p σ n (c • x) =
      complexGalois p σ c • complexDeRhamIntegerGradedGalois p σ n x := by
  apply (complexDeRhamIntegerGradedCoordinate p n).injective
  simp only [complexDeRhamIntegerGradedCoordinate_galois,
    complexDeRhamIntegerGradedCoordinate_complex_smul, map_mul]
  ring

end PadicHodgeTheory

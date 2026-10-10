/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartMultiplication
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The universal based algebra of a Hilbert chart

This is the actual free coordinate module over the equation quotient, endowed
with its universal multiplication table and unit. Rank zero is allowed.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)

/-- The free coordinate module, with a distinct type for its universal ring structure. -/
def UniversalAlgebra := Fin d → Coefficients R I d

instance : AddCommGroup (UniversalAlgebra R I d) :=
  inferInstanceAs (AddCommGroup (Fin d → Coefficients R I d))

instance : Module (Coefficients R I d) (UniversalAlgebra R I d) :=
  inferInstanceAs (Module (Coefficients R I d) (Fin d → Coefficients R I d))

instance : Mul (UniversalAlgebra R I d) := ⟨tableMul (mulCoeff R I d)⟩

instance : One (UniversalAlgebra R I d) := ⟨unitCoeff R I d⟩

instance : CommRing (UniversalAlgebra R I d) where
  __ := (inferInstance : AddCommGroup (UniversalAlgebra R I d))
  mul_assoc := tableMul_assoc _ (mulCoeff_assoc R I d)
  mul_comm := tableMul_comm _ (mulCoeff_comm R I d)
  one_mul := tableMul_unit_left _ _ (unitCoeff_mul R I d)
  mul_one a := (tableMul_comm _ (mulCoeff_comm R I d) a _).trans
    (tableMul_unit_left _ _ (unitCoeff_mul R I d) a)
  left_distrib := tableMul_add_right _
  right_distrib := tableMul_add_left _
  zero_mul a := by
    funext k
    change (∑ i, ∑ j, (0 : Coefficients R I d) * a j * mulCoeff R I d i j k) = 0
    simp only [zero_mul, Finset.sum_const_zero]
  mul_zero a := by
    funext k
    change (∑ i, ∑ j, a i * (0 : Coefficients R I d) * mulCoeff R I d i j k) = 0
    simp only [mul_zero, zero_mul, Finset.sum_const_zero]
  natCast n := n • (1 : UniversalAlgebra R I d)
  natCast_zero := zero_smul _ _
  natCast_succ n := AddMonoid.nsmul_succ n _
  intCast n := n • (1 : UniversalAlgebra R I d)
  intCast_ofNat := natCast_zsmul _
  intCast_negSucc := negSucc_zsmul _

instance : Algebra (Coefficients R I d) (UniversalAlgebra R I d) :=
  Algebra.ofModule (tableMul_smul_left _) fun r a b ↦
    (tableMul_comm _ (mulCoeff_comm R I d) a (r • b)).trans
      ((tableMul_smul_left _ r b a).trans
        (congrArg (fun x : Fin d → Coefficients R I d ↦ r • x)
          (tableMul_comm _ (mulCoeff_comm R I d) b a)))

/-- The coordinates are a linear equivalence with the actual free coordinate module. -/
def coordinates : UniversalAlgebra R I d ≃ₗ[Coefficients R I d]
    (Fin d → Coefficients R I d) := LinearEquiv.refl _ _

/-- The actual distinguished basis of the universal algebra. -/
def basis : Module.Basis (Fin d) (Coefficients R I d) (UniversalAlgebra R I d) :=
  (Pi.basisFun (Coefficients R I d) (Fin d)).map (coordinates R I d).symm

instance : Module.Free (Coefficients R I d) (UniversalAlgebra R I d) :=
  Module.Free.of_basis (basis R I d)

instance : Module.Finite (Coefficients R I d) (UniversalAlgebra R I d) :=
  Module.Finite.of_basis (basis R I d)

/-- Multiplication really uses the universal structure constants. -/
theorem coordinates_mul (a b : UniversalAlgebra R I d) (k : Fin d) :
    coordinates R I d (a * b) k =
      ∑ i, ∑ j, coordinates R I d a i * coordinates R I d b j * mulCoeff R I d i j k :=
  rfl

/-- The unit has precisely the declared universal coordinates. -/
theorem coordinates_one (k : Fin d) :
    coordinates R I d 1 k = unitCoeff R I d k := rfl

/-- The distinguished basis has the Kronecker-delta coordinates. -/
theorem coordinates_basis (i k : Fin d) :
    coordinates R I d (basis R I d i) k = if i = k then 1 else 0 := by
  change (Pi.basisFun (Coefficients R I d) (Fin d) i) k = _
  simp [Pi.single_apply, eq_comm]

end FLT.Mazur.HilbertChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeAlgebraCharpoly

/-!
# Characteristic polynomials on a complete split finite algebra

A product decomposition of the whole algebra computes its characteristic
polynomial. The formula retains every coordinate, including an empty frame,
and works over arbitrary coefficient rings.
-/

@[expose] public noncomputable section
open Polynomial Module TensorProduct
open scoped BigOperators
namespace FLT.Mazur.FiniteFreeAlgebraCharpoly
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
  {ι I : Type*} [Finite ι] [Fintype I] (b : Basis ι R B)

/-- Multiplication in the full product has the expected diagonal characteristic polynomial. -/
theorem charpoly_pi (x : I → R) :
    charpoly (Pi.basisFun R I) x = ∏ i, (X - C (x i)) := by
  classical
  let _ := Module.Free.of_basis (Pi.basisFun R I)
  let _ := Module.Finite.of_basis (Pi.basisFun R I)
  change (Algebra.lmul R (I → R) x).charpoly = _
  rw [← LinearMap.charpoly_toMatrix _ (Pi.basisFun R I)]
  have hm : LinearMap.toMatrix (Pi.basisFun R I) (Pi.basisFun R I)
      (Algebra.lmul R (I → R) x) = Matrix.diagonal x := by
    ext i j
    simp [Matrix.diagonal_apply]
    split_ifs with h
    · subst j
      simp
    · simp [h]
  rw [hm, Matrix.charpoly_diagonal]

/-- A full algebra decomposition constructs the splitting over its original base. -/
theorem charpoly_split (e : B ≃ₐ[R] (I → R)) (x : B) :
    charpoly b x = ∏ i, (X - C (e x i)) := by
  rw [← transport b (Pi.basisFun R I) e x, charpoly_pi]

variable (T : Type*) [CommRing T] [Algebra R T]

/-- An arbitrary complete split scalar extension computes every mapped coefficient. -/
theorem charpoly_split_baseChange (e : (T ⊗[R] B) ≃ₐ[T] (I → T)) (x : B) :
    (charpoly b x).map (algebraMap R T) = ∏ i, (X - C (e (1 ⊗ₜ[R] x) i)) := by
  rw [← baseChange b T, charpoly_split (b.baseChange T) e]

end FLT.Mazur.FiniteFreeAlgebraCharpoly

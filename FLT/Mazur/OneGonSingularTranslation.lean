/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSplitTangentNormalForm

/-!
# Centering residual nodes over arbitrary coefficient rings

Translate a specified residual singular point before adjoining a tangent.
Vanishing of the equation and both derivatives gives the needed coefficient
congruences over any ring, without assuming the residue is a field.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.OneGonInfinitesimal
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- Translation of the original affine coordinates by the specified point. -/
def centerChange (x y : R) : VariableChange R := ⟨1, x, 0, y⟩

/-- The original equation translated to the specified center. -/
def centeredEquation (x y : R) : WeierstrassCurve R := centerChange x y • W

/-- Centering commutes with every coefficient homomorphism. -/
theorem centeredEquation_map {A : Type} [CommRing A] (f : R →+* A) (x y : R) :
    (centeredEquation W x y).map f = centeredEquation (W.map f) (f x) (f y) := by
  rw [centeredEquation, ← map_variableChange, centeredEquation]
  congr 1
  ext <;> simp [centerChange, VariableChange.map]

/-- The tangent discriminant at the specified point, with its integral coefficient twelve. -/
theorem centeredEquation_b₂ (x y : R) : (centeredEquation W x y).b₂ = W.b₂ + 12 * x := by
  simp only [centeredEquation, centerChange, b₂, variableChange_a₁, variableChange_a₂,
    inv_one, Units.val_one, one_pow, one_mul, zero_mul,
    zero_pow (by decide : 2 ≠ 0), sub_zero]
  ring

/-- A specified critical zero becomes a centered nodal equation over any ring. -/
theorem centeredEquation_singular (x y : R) (he : W.toAffine.Equation x y)
    (hx : W.toAffine.polynomialX.evalEval x y = 0)
    (hy : W.toAffine.polynomialY.evalEval x y = 0) :
    (centeredEquation W x y).a₃ = 0 ∧ (centeredEquation W x y).a₄ = 0 ∧
      (centeredEquation W x y).a₆ = 0 := by
  rw [Affine.evalEval_polynomialX] at hx
  rw [Affine.evalEval_polynomialY] at hy
  refine ⟨?_, ?_, ?_⟩
  · simp only [centeredEquation, centerChange, variableChange_a₃, inv_one, Units.val_one,
      one_pow, one_mul]
    linear_combination hy
  · simp only [centeredEquation, centerChange, variableChange_a₄, inv_one, Units.val_one,
      one_pow, one_mul]
    linear_combination -hx
  · exact Affine.equation_zero.mp ((Affine.equation_iff_variableChange x y).mp he)

/-- Residual critical-point equations give all three original ideal congruences. -/
theorem centeredEquation_residual (I : Ideal R) (x y : R)
    (he : (W.map (Ideal.Quotient.mk I)).toAffine.Equation
      (Ideal.Quotient.mk I x) (Ideal.Quotient.mk I y))
    (hx : (W.map (Ideal.Quotient.mk I)).toAffine.polynomialX.evalEval
      (Ideal.Quotient.mk I x) (Ideal.Quotient.mk I y) = 0)
    (hy : (W.map (Ideal.Quotient.mk I)).toAffine.polynomialY.evalEval
      (Ideal.Quotient.mk I x) (Ideal.Quotient.mk I y) = 0) :
    (centeredEquation W x y).a₃ ∈ I ∧ (centeredEquation W x y).a₄ ∈ I ∧
      (centeredEquation W x y).a₆ ∈ I := by
  have h := centeredEquation_singular (W.map (Ideal.Quotient.mk I)) _ _ he hx hy
  rw [← centeredEquation_map] at h
  exact ⟨Ideal.Quotient.eq_zero_iff_mem.mp h.1,
    Ideal.Quotient.eq_zero_iff_mem.mp h.2.1, Ideal.Quotient.eq_zero_iff_mem.mp h.2.2⟩

end FLT.Mazur.OneGonInfinitesimal

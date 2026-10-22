/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingEquation
public import FLT.Mazur.EllipticNormalizedSingularity

/-!
# Normalizing an original split ordinary nodal equation

A chosen simple tangent root supplies an admissible shear and scaling to the
standard one-gon equation. Translating an arbitrary singular point first gives
the same conclusion without fixing its coordinates in advance.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.OneGonInfinitesimal
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The tangent shear and scaling, using the actual invertible tangent derivative. -/
def splitTangentChange (s : R) (hs : IsUnit (W.a₁ + 2 * s)) : VariableChange R :=
  ⟨hs.neg.unit, 0, s, 0⟩

/-- A centered nodal equation with a simple split tangent has the standard integral form. -/
theorem splitTangentChange_equation (s : R) (hs : IsUnit (W.a₁ + 2 * s))
    (hslope : s ^ 2 + W.a₁ * s = W.a₂)
    (h₃ : W.a₃ = 0) (h₄ : W.a₄ = 0) (h₆ : W.a₆ = 0) :
    splitTangentChange W s hs • W = OneGonSmoothing.equation 0 := by
  apply WeierstrassCurve.ext
  · rw [variableChange_a₁]
    change (↑(hs.neg.unit⁻¹) : R) * (W.a₁ + 2 * s) = -1
    have hu : W.a₁ + 2 * s = -(hs.neg.unit : R) := by rw [hs.neg.unit_spec, neg_neg]
    simpa only [mul_neg, Units.inv_mul] using
      congrArg (fun z : R => (↑(hs.neg.unit⁻¹) : R) * z) hu
  · rw [variableChange_a₂]
    have he : W.a₂ - s * W.a₁ + 3 * (0 : R) - s ^ 2 = 0 := by
      linear_combination -hslope
    change _ * (W.a₂ - s * W.a₁ + 3 * (0 : R) - s ^ 2) = 0
    rw [he, mul_zero]
  · simp only [variableChange_a₃, splitTangentChange, h₃, zero_mul, mul_zero,
      add_zero, OneGonSmoothing.equation]
  · simp only [variableChange_a₄, splitTangentChange, h₃, h₄, zero_mul, mul_zero,
      add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), OneGonSmoothing.equation]
  · simp only [variableChange_a₆, splitTangentChange, h₃, h₄, h₆, zero_mul, mul_zero,
      add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
      zero_pow (by decide : 3 ≠ 0), OneGonSmoothing.equation]

/-- The original tangent discriminant is a unit exactly as expected for an ordinary node. -/
theorem splitTangent_discriminant (s : R) (hslope : s ^ 2 + W.a₁ * s = W.a₂) :
    W.a₁ ^ 2 + 4 * W.a₂ = (W.a₁ + 2 * s) ^ 2 := by
  linear_combination -4 * hslope

variable {K : Type*} [Field K] (V : WeierstrassCurve K)

/-- An arbitrary singular point with a simple rational tangent has a pointed nodal normal form. -/
theorem singular_point_normalForm (x y s : K)
    (he : V.toAffine.Equation x y) (hn : ¬ V.toAffine.Nonsingular x y)
    (hslope : s ^ 2 + V.a₁ * s = V.a₂ + 3 * x)
    (hs : IsUnit (V.a₁ + 2 * s)) :
    ∃ C : VariableChange K, C • V = OneGonSmoothing.equation 0 := by
  let T : VariableChange K := ⟨1, x, 0, y⟩
  have h₁ : (T • V).a₁ = V.a₁ := by simp [T, variableChange_a₁]
  have h₂ : (T • V).a₂ = V.a₂ + 3 * x := by simp [T, variableChange_a₂]
  obtain ⟨h₃, h₄, h₆⟩ := translated_singular_coefficients V he hn
  have hu : IsUnit ((T • V).a₁ + 2 * s) := by rw [h₁]; exact hs
  refine ⟨splitTangentChange (T • V) s hu * T, ?_⟩
  rw [mul_smul]
  exact splitTangentChange_equation (T • V) s hu
    (by rw [h₁, h₂]; exact hslope) h₃ h₄ h₆

end FLT.Mazur.OneGonInfinitesimal

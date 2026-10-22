/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNilpotentGeneralizedPresentation
public import FLT.Mazur.OneGonSplitTangentNormalForm

/-!
# Lifting an original residual nodal presentation

The reduced equation need not already have standard nodal coefficients. Any
admissible presentation of that original reduction lifts to a presentation of
the deformation, retaining exactly the originally specified residual change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.OneGonInfinitesimal
variable {R : Type} [CommRing R]

/-- Lift an original residual normal form through an arbitrary nilpotent thickening. -/
theorem residual_normalForm_lift (W : WeierstrassCurve R) (I : Ideal R)
    (hI : IsNilpotent I) (C₀ : VariableChange (R ⧸ I))
    (h₀ : C₀ • W.map (Ideal.Quotient.mk I) = OneGonSmoothing.equation 0) :
    ∃ (C : VariableChange R) (t : R), C • W = OneGonSmoothing.equation t ∧
      C.map (Ideal.Quotient.mk I) = C₀ ∧ t ∈ I ∧ IsUnit (1 + 432 * t) := by
  obtain ⟨D, hD⟩ := NilpotentVariableChange.exists_lift I hI C₀
  have hd : (D • W).map (Ideal.Quotient.mk I) = OneGonSmoothing.equation 0 := by
    rw [← map_variableChange, hD, h₀]
  obtain ⟨C, t, he, hc, ht, hu⟩ := exists_relative_presentation (D • W) I hI hd
  refine ⟨C * D, t, ?_, ?_, ht, hu⟩
  · simpa only [mul_smul] using he
  · change VariableChange.mapHom (Ideal.Quotient.mk I) (C * D) = C₀
    rw [map_mul]
    change C.map (Ideal.Quotient.mk I) * D.map (Ideal.Quotient.mk I) = C₀
    rw [hc, hD, one_mul]

/-- A simple split tangent on the original reduced equation gives a deformation normal form. -/
theorem residual_splitTangent_normalForm (W : WeierstrassCurve R) (I : Ideal R)
    (hI : IsNilpotent I) (s : R ⧸ I)
    (hs : IsUnit ((W.map (Ideal.Quotient.mk I)).a₁ + 2 * s))
    (hslope : s ^ 2 + (W.map (Ideal.Quotient.mk I)).a₁ * s =
      (W.map (Ideal.Quotient.mk I)).a₂)
    (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) (h₆ : W.a₆ ∈ I) :
    ∃ (C : VariableChange R) (t : R), C • W = OneGonSmoothing.equation t ∧
      t ∈ I ∧ IsUnit (1 + 432 * t) := by
  let V := W.map (Ideal.Quotient.mk I)
  have he := splitTangentChange_equation V s hs hslope
    (Ideal.Quotient.eq_zero_iff_mem.mpr h₃) (Ideal.Quotient.eq_zero_iff_mem.mpr h₄)
    (Ideal.Quotient.eq_zero_iff_mem.mpr h₆)
  obtain ⟨C, t, he, _, ht, hu⟩ := residual_normalForm_lift W I hI _ he
  exact ⟨C, t, he, ht, hu⟩

/-- The specified residual change lifts to a full arithmetic generalized-curve presentation. -/
theorem residual_full_presentation (W : WeierstrassCurve R) (I : Ideal R)
    (hI : IsNilpotent I) (C₀ : VariableChange (R ⧸ I))
    (h₀ : C₀ • W.map (Ideal.Quotient.mk I) = OneGonSmoothing.equation 0) :
    ∃ (C : VariableChange R) (t : R) (ht : IsUnit (1 + 432 * t))
      (he : C • W = OneGonSmoothing.equation t),
      C.map (Ideal.Quotient.mk I) = C₀ ∧ t ∈ I ∧
        Nonempty (curveOfNormalForm W t C he ht ≅
          ArithmeticOneGonParameter.universalCurve.baseChange
            (ArithmeticOneGonParameter.parameterMap t ht)) := by
  obtain ⟨C, t, he, hc, hi, ht⟩ := residual_normalForm_lift W I hI C₀ h₀
  exact ⟨C, t, ht, he, hc, hi, ⟨(generalizedNormalFormIso W t C he ht).symm ≪≫
    ArithmeticOneGonParameter.specializationIso t ht⟩⟩

end FLT.Mazur.OneGonInfinitesimal

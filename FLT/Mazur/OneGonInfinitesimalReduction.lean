/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSquareZeroNormalForm
public import FLT.Mazur.NilpotentVariableChangeLifting

/-!
# Retaining the original nodal reduction under normalization

The explicit change reduces to the identity, so the normalization is relative
to the given nodal coordinates. Coefficient congruences can be recovered from
an actual equality of reduced equations at any intermediate thickening.
-/

@[expose] public noncomputable section
open WeierstrassCurve
namespace FLT.Mazur.OneGonInfinitesimal
variable {R : Type*} [CommRing R]

/-- An equation with reduced one-gon normal form has precisely the four required errors. -/
theorem coefficients_mem_of_map_eq (W : WeierstrassCurve R) (I : Ideal R)
    (t : R ⧸ I) (h : W.map (Ideal.Quotient.mk I) = OneGonSmoothing.equation t) :
    W.a₁ + 1 ∈ I ∧ W.a₂ ∈ I ∧ W.a₃ ∈ I ∧ W.a₄ ∈ I := by
  have h₁ := congrArg WeierstrassCurve.a₁ h
  have h₂ := congrArg WeierstrassCurve.a₂ h
  have h₃ := congrArg WeierstrassCurve.a₃ h
  have h₄ := congrArg WeierstrassCurve.a₄ h
  refine ⟨?_, Ideal.Quotient.eq_zero_iff_mem.mp h₂,
    Ideal.Quotient.eq_zero_iff_mem.mp h₃, Ideal.Quotient.eq_zero_iff_mem.mp h₄⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk I W.a₁ = -1 at h₁
  rw [map_add, map_one, h₁, neg_add_cancel]

/-- The explicit first-order normalizing change fixes the original reduction. -/
theorem squareZero_change_map (W : WeierstrassCurve R) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (h₁ : W.a₁ + 1 ∈ I) (h₂ : W.a₂ ∈ I) (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) :
    (OneGonSquareZero.change W (OneGonSquareZero.scaleError_square W I hI h₁ h₂ h₃ h₄)).map
      (Ideal.Quotient.mk I) = 1 := by
  apply (NilpotentVariableChange.map_eq_one_iff I _).mpr
  refine ⟨?_, OneGonSquareZero.shiftX_mem W I h₃ h₄,
    OneGonSquareZero.shear_mem W I h₂ h₃ h₄, OneGonSquareZero.shiftY_mem W I h₄⟩
  change 1 + OneGonSquareZero.scaleError W - 1 ∈ I
  simpa only [add_sub_cancel_left] using OneGonSquareZero.scaleError_mem W I h₁ h₂ h₃ h₄

/-- Every square-zero deformation is normalized relative to its original reduction. -/
theorem squareZero_normalForm (W : WeierstrassCurve R) (I : Ideal R) (hI : I ^ 2 = ⊥)
    (h₁ : W.a₁ + 1 ∈ I) (h₂ : W.a₂ ∈ I) (h₃ : W.a₃ ∈ I) (h₄ : W.a₄ ∈ I) :
    ∃ (C : VariableChange R) (t : R), C • W = OneGonSmoothing.equation t ∧
      C.map (Ideal.Quotient.mk I) = 1 := by
  refine ⟨OneGonSquareZero.change W
    (OneGonSquareZero.scaleError_square W I hI h₁ h₂ h₃ h₄), _,
    OneGonSquareZero.change_normalForm W I hI h₁ h₂ h₃ h₄, ?_⟩
  exact squareZero_change_map W I hI h₁ h₂ h₃ h₄

/-- The normalized parameter retains the original constant coefficient modulo the ideal. -/
theorem parameter_congr (W : WeierstrassCurve R) (I : Ideal R) (C : VariableChange R)
    (t : R) (h : C • W = OneGonSmoothing.equation t)
    (hC : C.map (Ideal.Quotient.mk I) = 1) : t - W.a₆ ∈ I := by
  have he := congrArg (fun V : WeierstrassCurve R => V.map (Ideal.Quotient.mk I)) h
  rw [← map_variableChange, hC, one_smul, OneGonSmoothing.equation_map] at he
  have ht := congrArg WeierstrassCurve.a₆ he
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact sub_eq_zero.mpr ht.symm

end FLT.Mazur.OneGonInfinitesimal

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# The integral-basis norm on convolution functionals

For a finite free coalgebra over a ring whose scalars have norm at most one,
the maximum of a functional on an integral basis is submultiplicative.
The resulting convolution algebra is complete when the coefficient field is.
-/

@[expose] public noncomputable section

open WithConv

namespace Module.Basis

variable {R A E ι : Type*} [CommRing R] [AddCommGroup A] [Module R A]
  [NontriviallyNormedField E] [Algebra R E] [Fintype ι]
  (b : Module.Basis ι R A)

/-- Coordinates of a convolution functional are its values on a basis. -/
def convolutionCoordinates : WithConv (A →ₗ[R] E) ≃ₗ[E] (ι → E) :=
  (WithConv.linearEquiv E _).trans (b.constr E).symm

/-- The maximum norm on values at an integral basis. -/
abbrev convolutionNormedAddCommGroup : NormedAddCommGroup (WithConv (A →ₗ[R] E)) :=
  NormedAddCommGroup.induced _ _ (b.convolutionCoordinates (E := E))
    (b.convolutionCoordinates (E := E)).injective

/-- Scalar multiplication is normed for the integral-basis norm. -/
abbrev convolutionNormedSpace :
    letI _convolutionNorm := b.convolutionNormedAddCommGroup (E := E)
    NormedSpace E (WithConv (A →ₗ[R] E)) :=
  NormedSpace.induced E _ _ (b.convolutionCoordinates (E := E))

/-- The coordinate equivalence is an isometry for the integral-basis norm. -/
def convolutionCoordinateIsometry :
    letI _convolutionNorm := b.convolutionNormedAddCommGroup (E := E)
    WithConv (A →ₗ[R] E) ≃ₗᵢ[E] (ι → E) :=
  letI _convolutionNorm := b.convolutionNormedAddCommGroup (E := E)
  { b.convolutionCoordinates with norm_map' := fun _ ↦ rfl }

/-- A finite convolution space over a complete field is complete. -/
theorem convolution_completeSpace [CompleteSpace E] :
    letI _convolutionNorm := b.convolutionNormedAddCommGroup (E := E)
    CompleteSpace (WithConv (A →ₗ[R] E)) := by
  let convolutionNorm := b.convolutionNormedAddCommGroup (E := E)
  exact (b.convolutionCoordinateIsometry.toIsometryEquiv.completeSpace_iff).mpr inferInstance

/-- The convolution norm is the maximum of the values on the basis. -/
theorem convolution_norm_eq (F : WithConv (A →ₗ[R] E)) :
    letI _convolutionNorm := b.convolutionNormedAddCommGroup (E := E)
    ‖F‖ = ‖fun i ↦ F (b i)‖ := rfl

/-- A common bound on summands bounds their sum for a nonarchimedean norm. -/
theorem norm_sum_le_of_nonarchimedean (hna : IsNonarchimedean (norm : E → ℝ))
    {κ : Type*} (s : Finset κ) (f : κ → E) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ c) : ‖∑ i ∈ s, f i‖ ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hc
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hna _ _).trans (max_le (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))))

/-- An integral input cannot increase the integral-basis norm of a functional. -/
theorem norm_apply_le_convolution_norm
    (hna : IsNonarchimedean (norm : E → ℝ))
    (hR : ∀ r : R, ‖algebraMap R E r‖ ≤ 1)
    (F : WithConv (A →ₗ[R] E)) (a : A) :
    letI _convolutionNorm := b.convolutionNormedAddCommGroup (E := E)
    ‖F a‖ ≤ ‖F‖ := by
  let convolutionNorm := b.convolutionNormedAddCommGroup (E := E)
  rw [← b.sum_repr a, map_sum]
  apply norm_sum_le_of_nonarchimedean hna _ _ (norm_nonneg _)
  intro i _
  rw [map_smul, Algebra.smul_def, norm_mul]
  calc
    _ ≤ 1 * ‖F (b i)‖ := mul_le_mul_of_nonneg_right (hR _) (norm_nonneg _)
    _ ≤ ‖F‖ := by simpa only [one_mul, b.convolution_norm_eq] using
      norm_le_pi_norm (fun j ↦ F (b j)) i

/-- The integral-basis norm satisfies the ultrametric inequality. -/
theorem convolution_isNonarchimedean (hna : IsNonarchimedean (norm : E → ℝ)) :
    letI _convolutionNorm := b.convolutionNormedAddCommGroup (E := E)
    IsNonarchimedean (norm : WithConv (A →ₗ[R] E) → ℝ) := by
  let convolutionNorm := b.convolutionNormedAddCommGroup (E := E)
  intro F G
  rw [b.convolution_norm_eq]
  apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).mpr
  intro i
  exact (hna _ _).trans (max_le_max
    (norm_le_pi_norm (fun j ↦ F (b j)) i) (norm_le_pi_norm (fun j ↦ G (b j)) i))

variable [Coalgebra R A]

/-- The integral-basis norm is submultiplicative for convolution. -/
theorem convolution_norm_mul_le (hna : IsNonarchimedean (norm : E → ℝ))
    (hR : ∀ r : R, ‖algebraMap R E r‖ ≤ 1)
    (F G : WithConv (A →ₗ[R] E)) :
    letI _convolutionNorm := b.convolutionNormedAddCommGroup (E := E)
    ‖F * G‖ ≤ ‖F‖ * ‖G‖ := by
  let convolutionNorm := b.convolutionNormedAddCommGroup (E := E)
  rw [b.convolution_norm_eq]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
  intro i
  rw [(Coalgebra.Repr.arbitrary R (b i)).convMul_apply]
  apply norm_sum_le_of_nonarchimedean hna _ _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro j _
  rw [norm_mul]
  exact mul_le_mul (b.norm_apply_le_convolution_norm hna hR F _)
    (b.norm_apply_le_convolution_norm hna hR G _) (norm_nonneg _) (norm_nonneg _)

/-- The convolution ring equipped with the integral-basis norm. -/
abbrev convolutionNormedRing (hna : IsNonarchimedean (norm : E → ℝ))
    (hR : ∀ r : R, ‖algebraMap R E r‖ ≤ 1) : NormedRing (WithConv (A →ₗ[R] E)) :=
  { b.convolutionNormedAddCommGroup (E := E),
    (inferInstance : Ring (WithConv (A →ₗ[R] E))) with
    norm_mul_le := b.convolution_norm_mul_le hna hR }

/-- The convolution algebra equipped with the integral-basis norm. -/
abbrev convolutionNormedAlgebra (hna : IsNonarchimedean (norm : E → ℝ))
    (hR : ∀ r : R, ‖algebraMap R E r‖ ≤ 1) :
    letI _convolutionRing := b.convolutionNormedRing hna hR
    NormedAlgebra E (WithConv (A →ₗ[R] E)) := by
  letI _convolutionRing := b.convolutionNormedRing hna hR
  letI _convolutionSpace := b.convolutionNormedSpace (E := E)
  exact ⟨norm_smul_le⟩

/-- Cocommutativity makes the normed convolution ring commutative. -/
abbrev convolutionNormedCommRing [Coalgebra.IsCocomm R A]
    (hna : IsNonarchimedean (norm : E → ℝ))
    (hR : ∀ r : R, ‖algebraMap R E r‖ ≤ 1) : NormedCommRing (WithConv (A →ₗ[R] E)) :=
  { b.convolutionNormedRing hna hR,
    (inferInstance : CommRing (WithConv (A →ₗ[R] E))) with }

end Module.Basis

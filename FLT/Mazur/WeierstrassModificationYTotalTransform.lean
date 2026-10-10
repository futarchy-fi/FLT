/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYSaturation

/-!
# The original cubic on the saturated y-direction chart

The original substitution is x=z*u, y=z, with r*z=s retained. An explicit
incidence multiple compares its total transform with z² times the divided
cubic. Thus vertical saturation recovers the actual y-direction algebra.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace FLT.Mazur.WeierstrassModificationY

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The original cubic after x=z*u, y=z. -/
def originalTransformPolynomial : MvPolynomial (Fin 3) R :=
  X 2 ^ 2 + C W.a₁ * (X 2 * X 1) * X 2 + C W.a₃ * X 2 -
    ((X 2 * X 1) ^ 3 + C W.a₂ * (X 2 * X 1) ^ 2 + C W.a₄ * (X 2 * X 1) + C W.a₆)

/-- The total-transform relations with the original cubic retained. -/
def originalTransformRelations : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span {originalTransformPolynomial W, X 0 * X 2 - C s}

/-- The correction between the original equation and the divided equation. -/
def transformCorrection : MvPolynomial (Fin 3) R :=
  -C b3 * X 2 + C b4 * X 2 * X 1 + C b6 * (C s + X 0 * X 2)

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h3 h4 h6

/-- The exact incidence correction in the original cubic. -/
theorem originalTransform_identity :
    originalTransformPolynomial W - X 2 ^ 2 * equationPolynomial W b3 b4 b6 =
      (X 0 * X 2 - C s) * transformCorrection s b3 b4 b6 := by
  simp only [originalTransformPolynomial, equationPolynomial, transformCorrection,
    h3, h4, h6, map_mul, map_pow]
  ring

/-- The actual original total transform generates exactly the expected relations. -/
theorem originalTransformRelations_eq :
    originalTransformRelations W s = totalRelations W s b3 b4 b6 := by
  have he := originalTransform_identity W s b3 b4 b6 h3 h4 h6
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · rw [eq_add_of_sub_eq he]
      apply Ideal.add_mem
      · exact Ideal.mul_mem_right _ _
          (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      · exact Ideal.subset_span (Set.mem_insert _ _)
    · have hp' := Set.mem_singleton_iff.mp hp
      subst p
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · rw [eq_sub_of_add_eq' (eq_add_of_sub_eq he).symm]
      apply Ideal.sub_mem
      · exact Ideal.subset_span (Set.mem_insert _ _)
      · exact Ideal.mul_mem_right _ _
          (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    · have hp' := Set.mem_singleton_iff.mp hp
      subst p
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

variable [IsDomain R] [IsBezout R]

/-- Vertical saturation of the original cubic gives the actual y-chart relations. -/
theorem originalTransform_saturation (hs : s ≠ 0) (p : MvPolynomial (Fin 3) R) :
    (∃ n : ℕ, X 2 ^ n * p ∈ originalTransformRelations W s) ↔
      p ∈ relations W s b3 b4 b6 := by
  rw [originalTransformRelations_eq W s b3 b4 b6 h3 h4 h6]
  exact totalRelations_saturation W s b3 b4 b6 h3 h4 h6 hs p

/-- Vanishing in the actual y-chart detects the saturated original total transform. -/
theorem originalTransform_saturation_iff_eval (hs : s ≠ 0) (p : MvPolynomial (Fin 3) R) :
    (∃ n : ℕ, X 2 ^ n * p ∈ originalTransformRelations W s) ↔
      aeval (coord W s b3 b4 b6) p = 0 := by
  rw [originalTransform_saturation W s b3 b4 b6 h3 h4 h6 hs, coord_aeval]
  exact Ideal.Quotient.eq_zero_iff_mem.symm

end FLT.Mazur.WeierstrassModificationY

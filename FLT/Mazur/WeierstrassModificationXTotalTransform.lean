/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXSaturation

/-!
# The saturated chart comes from the original Weierstrass equation

Substitute y=x*v into the original cubic while retaining t*x=s. Modulo this
incidence equation, the total transform is minus x² times the strict equation.
Consequently the proved saturation describes the original equation itself,
with all three coefficient divisibility hypotheses explicitly retained.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace FLT.Mazur.WeierstrassModificationX

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The original Weierstrass equation after the actual substitution y=x*v. -/
def originalTransformPolynomial : MvPolynomial (Fin 3) R :=
  (X 2 * X 1) ^ 2 + C W.a₁ * X 2 * (X 2 * X 1) + C W.a₃ * (X 2 * X 1) -
    (X 2 ^ 3 + C W.a₂ * X 2 ^ 2 + C W.a₄ * X 2 + C W.a₆)

/-- The incidence equation and the actual original cubic on the x-direction chart. -/
def originalTransformRelations : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span {incidencePolynomial s, originalTransformPolynomial W}

/-- The exact correction multiple of the incidence equation. -/
def transformCorrection : MvPolynomial (Fin 3) R :=
  -C b3 * X 2 * X 1 + C b4 * X 2 + (C s + X 0 * X 2) * C b6

variable (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

include h3 h4 h6

/-- Dividing the original cubic differs only by an explicit incidence multiple. -/
theorem originalTransform_identity :
    originalTransformPolynomial W + X 2 ^ 2 * strictPolynomial W b3 b4 b6 =
      incidencePolynomial s * transformCorrection s b3 b4 b6 := by
  simp only [originalTransformPolynomial, strictPolynomial, horizontalPolynomial,
    incidencePolynomial, transformCorrection, h3, h4, h6, map_mul, map_pow]
  ring

/-- The total-transform ideal is exactly the one generated from the original cubic. -/
theorem originalTransformRelations_eq :
    originalTransformRelations W s = totalRelations W s b3 b4 b6 := by
  have he := originalTransform_identity W s b3 b4 b6 h3 h4 h6
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · have hp' := Set.mem_singleton_iff.mp hp
      subst p
      rw [eq_sub_of_add_eq he]
      apply Ideal.sub_mem
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
      · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · have hp' := Set.mem_singleton_iff.mp hp
      subst p
      rw [eq_sub_of_add_eq' he]
      apply Ideal.sub_mem
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
      · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

variable [IsDomain R]

/-- The actual equation chart is the horizontal saturation of the original cubic transform. -/
theorem originalTransform_saturation (hs : s ≠ 0) (p : MvPolynomial (Fin 3) R) :
    (∃ n : ℕ, X 2 ^ n * p ∈ originalTransformRelations W s) ↔
      p ∈ strictRelations W s b3 b4 b6 := by
  rw [originalTransformRelations_eq W s b3 b4 b6 h3 h4 h6]
  exact totalRelations_saturation W s b3 b4 b6 hs p

/-- Vanishing in the actual x-direction algebra detects the saturated original relations. -/
theorem originalTransform_saturation_iff_eval (hs : s ≠ 0) (p : MvPolynomial (Fin 3) R) :
    (∃ n : ℕ, X 2 ^ n * p ∈ originalTransformRelations W s) ↔
      aeval ![t W s b3 b4 b6, v W s b3 b4 b6, x W s b3 b4 b6] p = 0 := by
  rw [originalTransform_saturation W s b3 b4 b6 h3 h4 h6 hs]
  have h := (strictCoordinateEquiv W s b3 b4 b6).injective.eq_iff
    (a := Ideal.Quotient.mk _ p) (b := 0)
  rw [map_zero] at h
  exact Ideal.Quotient.eq_zero_iff_mem.symm.trans h.symm

end FLT.Mazur.WeierstrassModificationX

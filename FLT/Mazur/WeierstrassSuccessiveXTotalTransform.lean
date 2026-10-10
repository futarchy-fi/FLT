/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXSaturation

/-!
# Saturating the preceding divided cubic

The preceding equation has cubic coefficient s, not necessarily a unit.
After y=u*v its difference from u² times the successive equation is an
explicit multiple of t*u-π. Saturation therefore gives exactly the actual
three-generator chart, with the retained horizontal coordinate u.
-/

@[expose] public noncomputable section

open MvPolynomial

namespace FLT.Mazur.WeierstrassSuccessiveX

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- The preceding divided equation after the substitution (x,y)=(u,u*v). -/
def previousTransformPolynomial : MvPolynomial (Fin 3) R :=
  (X 2 * X 1) ^ 2 + (C W.a₁ * X 2 + C (π * b3)) * (X 2 * X 1) -
    (C s * X 2 ^ 3 + C W.a₂ * X 2 ^ 2 + C (π * b4) * X 2 + C (π ^ 2 * b6))

/-- The actual total-transform relations, before saturation. -/
def previousTransformRelations : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span {X 0 * X 2 - C π, previousTransformPolynomial W s π b3 b4 b6}

/-- The explicit correction by the incidence equation. -/
def transformCorrection : MvPolynomial (Fin 3) R :=
  -C b3 * X 2 * X 1 + C b4 * X 2 + (C π + X 0 * X 2) * C b6

/-- Dividing by u² preserves the preceding equation modulo incidence. -/
theorem previousTransform_identity :
    previousTransformPolynomial W s π b3 b4 b6 -
      X 2 ^ 2 * equationPolynomial W s b3 b4 b6 =
      (X 0 * X 2 - C π) * transformCorrection π b3 b4 b6 := by
  simp only [previousTransformPolynomial, equationPolynomial, transformCorrection, map_mul, map_pow]
  ring

/-- The actual preceding total transform has the proved saturation presentation. -/
theorem previousTransformRelations_eq :
    previousTransformRelations W s π b3 b4 b6 = totalRelations W s π b3 b4 b6 := by
  have he := previousTransform_identity W s π b3 b4 b6
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · have hp' := Set.mem_singleton_iff.mp hp
      subst p
      rw [eq_add_of_sub_eq he]
      apply Ideal.add_mem
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
      · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · have hp' := Set.mem_singleton_iff.mp hp
      subst p
      have he' : X 2 ^ 2 * equationPolynomial W s b3 b4 b6 =
          previousTransformPolynomial W s π b3 b4 b6 -
            (X 0 * X 2 - C π) * transformCorrection π b3 b4 b6 := by
        linear_combination -he
      rw [he']
      apply Ideal.sub_mem
      · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))

/-- Saturating the preceding cubic gives precisely the successive equation relations. -/
theorem previousTransform_saturation [IsDomain R] (hπ : π ≠ 0)
    (p : MvPolynomial (Fin 3) R) :
    (∃ n : ℕ, X 2 ^ n * p ∈ previousTransformRelations W s π b3 b4 b6) ↔
      p ∈ relations W s π b3 b4 b6 := by
  rw [previousTransformRelations_eq]
  exact totalRelations_saturation W s π b3 b4 b6 hπ p

/-- The actual chart's evaluation detects the saturated preceding cubic. -/
theorem previousTransform_saturation_iff_eval [IsDomain R] (hπ : π ≠ 0)
    (p : MvPolynomial (Fin 3) R) :
    (∃ n : ℕ, X 2 ^ n * p ∈ previousTransformRelations W s π b3 b4 b6) ↔
      aeval (coord W s π b3 b4 b6) p = 0 := by
  rw [previousTransform_saturation W s π b3 b4 b6 hπ, coord_aeval]
  exact Ideal.Quotient.eq_zero_iff_mem.symm

end FLT.Mazur.WeierstrassSuccessiveX
